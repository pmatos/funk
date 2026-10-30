//! Integer attributes, which have no limit of their own.
//!
//! An integer attribute is a value of its dialect: the dialect that reads it
//! bounds it, as a core constant must fit its type (`lean/Fir/Text/Lexical.lean`,
//! "Numbers"). A width goes up to 16,777,215 bits, so `Int` holds the canonical
//! decimal spelling, and [`Nat`] is the small unsigned big integer that checks
//! whether a value fits a width.

use std::fmt;

/// Bounds on log2(10) = 3.32192809..., as multiples of 2^-15.
const LOG2_10_LOW: u128 = 108_852;
const LOG2_10_HIGH: u128 = 108_853;

/// An integer, held as its one spelling: no leading zeros, no `+`, no `-0`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Int(String);

impl Int {
    /// The integer spelled `s`, if `s` is a canonical spelling.
    pub fn parse(s: &str) -> Option<Int> {
        let digits = s.strip_prefix('-').unwrap_or(s);
        let canonical = match digits.as_bytes() {
            [] => false,
            [b'0'] => digits.len() == s.len(),
            [first, rest @ ..] => {
                (b'1'..=b'9').contains(first) && rest.iter().all(u8::is_ascii_digit)
            }
        };
        canonical.then(|| Int(s.to_string()))
    }

    /// The integer with this sign and magnitude. Zero is never negative.
    pub fn from_nat(negative: bool, magnitude: &Nat) -> Int {
        let digits = magnitude.to_decimal();
        if negative && digits != "0" {
            Int(format!("-{digits}"))
        } else {
            Int(digits)
        }
    }

    /// The canonical spelling.
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// Whether the integer is below zero.
    pub fn is_negative(&self) -> bool {
        self.0.starts_with('-')
    }

    /// The decimal digits of the absolute value.
    pub fn magnitude_digits(&self) -> &str {
        self.0.strip_prefix('-').unwrap_or(&self.0)
    }

    /// Whether the integer is a two's-complement value of `width` bits:
    /// `-2^(w-1) <= v < 2^(w-1)`. At width 0, only `0` fits.
    pub fn fits_signed(&self, width: u32) -> bool {
        let digits = self.magnitude_digits();
        if width == 0 {
            return digits == "0";
        }
        let room = u64::from(width) - 1;
        let len = digits.len() as u128;
        // The magnitude v has len digits: 10^(len-1) <= v < 10^len. With
        // LOG2_10_LOW < log2(10) < LOG2_10_HIGH, both over 2^15, these
        // bounds decide every length except about 48 near the width's
        // limit, without converting the digits.
        if (len - 1) * LOG2_10_LOW > u128::from(room) << 15 {
            // v >= 10^(len-1) > 2^room.
            return false;
        }
        if len * LOG2_10_HIGH <= u128::from(room) << 15 {
            // v < 10^len < 2^room.
            return true;
        }
        let magnitude = Nat::from_decimal(digits);
        let bits = magnitude.bit_len();
        bits <= room || (self.is_negative() && bits == room + 1 && magnitude.is_power_of_two())
    }
}

impl From<i128> for Int {
    fn from(v: i128) -> Int {
        Int(v.to_string())
    }
}

impl fmt::Display for Int {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// An unsigned integer of any size, as little-endian 32-bit limbs with no
/// high zero limb.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Nat(Vec<u32>);

const CHUNK: u32 = 1_000_000_000;

impl Nat {
    /// The value of a string of decimal digits.
    pub fn from_decimal(digits: &str) -> Nat {
        let mut n = Nat(Vec::new());
        let bytes = digits.as_bytes();
        let head = bytes.len() % 9;
        let chunks = std::iter::once(&bytes[..head]).chain(bytes[head..].chunks(9));
        for chunk in chunks.filter(|c| !c.is_empty()) {
            let value = chunk.iter().fold(0u32, |a, d| a * 10 + u32::from(d - b'0'));
            let scale = 10u32.pow(chunk.len() as u32);
            n.mul_add(scale, value);
        }
        n
    }

    /// The value of a `u128`.
    pub fn from_u128(mut v: u128) -> Nat {
        let mut limbs = Vec::new();
        while v != 0 {
            limbs.push(v as u32);
            v >>= 32;
        }
        Nat(limbs)
    }

    /// `2^k - 1`: `k` one bits.
    pub fn ones(k: u64) -> Nat {
        let mut limbs = vec![u32::MAX; (k / 32) as usize];
        if !k.is_multiple_of(32) {
            limbs.push((1u32 << (k % 32)) - 1);
        }
        Nat(limbs)
    }

    /// `2^k`.
    pub fn pow2(k: u64) -> Nat {
        let mut limbs = vec![0; (k / 32) as usize];
        limbs.push(1 << (k % 32));
        Nat(limbs)
    }

    /// The number of bits needed to write the value; 0 for zero.
    pub fn bit_len(&self) -> u64 {
        match self.0.last() {
            None => 0,
            Some(top) => 32 * (self.0.len() as u64 - 1) + u64::from(32 - top.leading_zeros()),
        }
    }

    /// Whether the value is a power of two.
    pub fn is_power_of_two(&self) -> bool {
        match self.0.split_last() {
            None => false,
            Some((top, rest)) => top.is_power_of_two() && rest.iter().all(|&l| l == 0),
        }
    }

    /// The decimal digits of the value, with no leading zeros.
    pub fn to_decimal(&self) -> String {
        let mut n = self.clone();
        let mut chunks = Vec::new();
        while !n.0.is_empty() {
            chunks.push(n.div_rem_small(CHUNK));
        }
        let mut out = chunks
            .pop()
            .map_or_else(|| "0".to_string(), |c| c.to_string());
        for c in chunks.iter().rev() {
            out.push_str(&format!("{c:09}"));
        }
        out
    }

    fn mul_add(&mut self, m: u32, a: u32) {
        let mut carry = u64::from(a);
        for limb in &mut self.0 {
            let v = u64::from(*limb) * u64::from(m) + carry;
            *limb = v as u32;
            carry = v >> 32;
        }
        if carry != 0 {
            self.0.push(carry as u32);
        }
    }

    fn div_rem_small(&mut self, d: u32) -> u32 {
        let mut rem = 0u64;
        for limb in self.0.iter_mut().rev() {
            let v = (rem << 32) | u64::from(*limb);
            *limb = (v / u64::from(d)) as u32;
            rem = v % u64::from(d);
        }
        while self.0.last() == Some(&0) {
            self.0.pop();
        }
        rem as u32
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn only_canonical_spellings_parse() {
        for ok in ["0", "7", "-1", "170141183460469231731687303715884105728"] {
            assert_eq!(Int::parse(ok).map(|i| i.to_string()), Some(ok.to_string()));
        }
        for bad in ["", "-", "-0", "007", "+1", "1a", " 1", "--1"] {
            assert_eq!(Int::parse(bad), None, "{bad:?}");
        }
    }

    #[test]
    fn decimal_conversion_round_trips() {
        for s in [
            "0",
            "1",
            "4294967296",
            "123456789012345678901234567890123456789",
        ] {
            assert_eq!(Nat::from_decimal(s).to_decimal(), s);
        }
        assert_eq!(Nat::pow2(127).to_decimal(), (1u128 << 127).to_string());
        assert_eq!(Nat::ones(64).to_decimal(), u64::MAX.to_string());
        assert_eq!(
            Nat::from_u128(u128::MAX).to_decimal(),
            u128::MAX.to_string()
        );
    }

    #[test]
    fn fits_signed_checks_both_bounds() {
        let fits = |s: &str, w| Int::parse(s).unwrap().fits_signed(w);
        assert!(fits("0", 0) && !fits("1", 0) && !fits("-1", 0));
        assert!(fits("0", 1) && fits("-1", 1) && !fits("1", 1));
        assert!(fits("127", 8) && !fits("128", 8) && fits("-128", 8) && !fits("-129", 8));
        let max = (1u128 << 127) - 1;
        assert!(fits(&max.to_string(), 128) && !fits(&(max + 1).to_string(), 128));
        assert!(fits(&format!("-{}", max + 1), 128) && !fits(&format!("-{}", max + 2), 128));
        let big = Nat::pow2(299).to_decimal();
        assert!(!fits(&big, 300) && fits(&format!("-{big}"), 300));
        assert!(fits("-1", 16_777_215) && !fits(&"9".repeat(40), 100));
    }

    /// Whether the integer fits, by converting it in full.
    fn fits_exactly(v: &Int, width: u32) -> bool {
        let room = u64::from(width) - 1;
        let magnitude = Nat::from_decimal(v.magnitude_digits());
        let bits = magnitude.bit_len();
        bits <= room || (v.is_negative() && bits == room + 1 && magnitude.is_power_of_two())
    }

    #[test]
    fn the_digit_count_bounds_agree_with_the_exact_check() {
        for width in 1..=700u32 {
            let room = u64::from(width) - 1;
            let edge = Nat::pow2(room);
            let mut values = vec![edge.to_decimal(), Nat::ones(room).to_decimal()];
            let digits = edge.to_decimal().len();
            for len in digits.saturating_sub(2).max(1)..=digits + 2 {
                values.push("9".repeat(len));
                values.push(format!("1{}", "0".repeat(len - 1)));
            }
            for magnitude in values {
                for negative in [false, true] {
                    let v = Int::from_nat(negative, &Nat::from_decimal(&magnitude));
                    assert_eq!(
                        v.fits_signed(width),
                        fits_exactly(&v, width),
                        "{v} at {width}"
                    );
                }
            }
        }
    }

    #[test]
    fn a_constant_of_millions_of_digits_is_decided_without_converting_it() {
        let start = std::time::Instant::now();
        let nines = Int::parse(&"9".repeat(5_000_000)).unwrap();
        assert!(nines.fits_signed(16_777_215));
        let big = Int::parse(&format!("1{}", "0".repeat(5_050_600))).unwrap();
        assert!(!big.fits_signed(16_777_215));
        let secs = start.elapsed().as_secs();
        assert!(secs < 20, "took {secs} s");
    }
}
