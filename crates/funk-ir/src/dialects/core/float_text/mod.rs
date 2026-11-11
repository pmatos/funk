//! The text of a float constant (`lean/Fir/Core/FloatText.lean`,
//! ADR-2026-11-11-1438).
//!
//! A value of `float<e,m>` has one spelling. A finite value of a format
//! with decimals, `2 <= e <= 15` and `1 <= m <= 112`, is the shortest
//! decimal that reads back to its bits; of two such, the nearer to the
//! value, and of two equally near, the one whose last digit is even. Its
//! digits are laid out plainly when its decimal exponent `E` lies in
//! `-4 <= E < 16`, as `1.5` or `0.0001`, and otherwise as `1.5e-7`. Every
//! other value, and every value of a wider format, is `0x` and its bits in
//! `ceil((1 + e + m) / 4)` lowercase hexadecimal digits.
//!
//! Reading a decimal rounds its exact value to nearest even at the format.
//! A literal decodes only when it is the spelling of the bits it reads as.
//! Before reading a decimal, the reader rejects one whose whole part or
//! fraction has more than 64 digits, or whose exponent is more than 9999 in
//! magnitude: no spelling has them.

mod big;

use std::cmp::Ordering;

use big::Big;

use crate::ir::names::is_float_lit;

/// The bounds that the reader checks before reading a decimal.
const MAX_DIGITS: usize = 64;
const MAX_EXP: i64 = 9999;

/// Whether the finite values of `float<e,m>` are spelled in decimal.
pub fn has_decimals(e: u32, m: u32) -> bool {
    (2..=15).contains(&e) && (1..=112).contains(&m)
}

/// A format with decimals: its fields and the bounds of its exponents.
#[derive(Clone, Copy)]
struct Format {
    e: u32,
    m: u32,
}

impl Format {
    fn bias(self) -> i64 {
        (1i64 << (self.e - 1)) - 1
    }

    fn sign(self) -> u128 {
        1 << (self.e + self.m)
    }

    /// The exponent of the quantum of subnormals, the smallest of all.
    fn min_quantum(self) -> i64 {
        1 - self.bias() - i64::from(self.m)
    }

    /// The bits of `-1^neg · d · 10^k`, rounded to nearest even.
    fn read(self, neg: bool, d: &Big, k: i64) -> u128 {
        let sign = if neg { self.sign() } else { 0 };
        if d.is_zero() {
            return sign;
        }
        let (num, den) = if k >= 0 {
            (d.mul_pow10(k as u64), Big::from_u128(1))
        } else {
            (d.clone(), Big::from_u128(1).mul_pow10(k.unsigned_abs()))
        };
        // `t = floor(log2 x)`, from the lengths of the two, then exactly.
        let mut t = num.bit_len() as i64 - den.bit_len() as i64;
        let (a, b) = scaled(&num, &den, t);
        if a < b {
            t -= 1;
        }
        let q = (t - i64::from(self.m)).max(self.min_quantum());
        let (a, b) = scaled(&num, &den, q);
        let (whole, rest) = a.div_rem(&b);
        let mut mant = whole.to_u128().expect("a quotient below 2^(m + 2)");
        match rest.shl(1).cmp(&b) {
            Ordering::Greater => mant += 1,
            Ordering::Equal => mant += mant & 1,
            Ordering::Less => {}
        }
        let mut q = q;
        if mant == 1 << (self.m + 1) {
            mant >>= 1;
            q += 1;
        }
        if mant < 1 << self.m {
            return sign | mant;
        }
        let biased = q + i64::from(self.m) + self.bias();
        let top = (1i64 << self.e) - 1;
        if biased >= top {
            return sign | ((top as u128) << self.m);
        }
        sign | ((biased as u128) << self.m) | (mant - (1 << self.m))
    }

    /// The decimal that spells the bits `b`, when they are a zero or
    /// finite and the search finds one.
    fn decimal(self, b: u128) -> Option<String> {
        let neg = b & self.sign() != 0;
        let field = (b >> self.m) & ((1 << self.e) - 1);
        let man = b & ((1 << self.m) - 1);
        let (mant, x) = match field {
            0 if man == 0 => return Some(if neg { "-0.0" } else { "0.0" }.to_string()),
            0 => (man, self.min_quantum()),
            f if f == (1 << self.e) - 1 => return None,
            f => (
                man | (1 << self.m),
                f as i64 - self.bias() - i64::from(self.m),
            ),
        };
        let num = Big::from_u128(mant).shl(x.max(0) as u64);
        let den = Big::from_u128(1).shl((-x).max(0) as u64);
        let top = dec_exponent(&num, &den);
        for n in 1..=i64::from(self.m) + 4 {
            let j = top - n + 1;
            let (a, d) = by_pow10(&num, &den, j);
            let (lo, rest) = a.div_rem(&d);
            let hi = lo.add(&Big::from_u128(1));
            let mut ok: Vec<&Big> = if rest.is_zero() {
                vec![&lo]
            } else {
                vec![&lo, &hi]
            };
            ok.retain(|c| self.read(neg, c, j) == b);
            let c = match ok.as_slice() {
                [c] => (*c).clone(),
                [_, _] => {
                    let below = rest.clone();
                    let above = hi.mul(&d).sub(&a);
                    if below < above || (below == above && lo.is_even()) {
                        lo
                    } else {
                        hi
                    }
                }
                _ => continue,
            };
            return Some(layout(neg, &c, j));
        }
        None
    }
}

/// `(a, b)` with `a / b = (num / den) / 2^q`.
fn scaled(num: &Big, den: &Big, q: i64) -> (Big, Big) {
    if q >= 0 {
        (num.clone(), den.shl(q as u64))
    } else {
        (num.shl(q.unsigned_abs()), den.clone())
    }
}

/// `(a, b)` with `a / b = (num / den) / 10^j`.
fn by_pow10(num: &Big, den: &Big, j: i64) -> (Big, Big) {
    if j >= 0 {
        (num.clone(), den.mul_pow10(j as u64))
    } else {
        (num.mul_pow10(j.unsigned_abs()), den.clone())
    }
}

/// `E` with `10^E <= num / den < 10^(E+1)`, for a positive rational.
fn dec_exponent(num: &Big, den: &Big) -> i64 {
    let at_least = |t: i64| {
        let (a, b) = by_pow10(num, den, t);
        a >= b
    };
    let mut t = ((num.bit_len() as i64 - den.bit_len() as i64) * 30103).div_euclid(100_000);
    while !at_least(t) {
        t -= 1;
    }
    while at_least(t + 1) {
        t += 1;
    }
    t
}

/// The text of `-1^neg · c · 10^j`, with `c > 0`.
fn layout(neg: bool, c: &Big, j: i64) -> String {
    let mut ds = c.to_digits();
    let mut j = j;
    while ds.len() > 1 && ds.ends_with('0') {
        ds.pop();
        j += 1;
    }
    let len = ds.len() as i64;
    let e = j + len - 1;
    let sign = if neg { "-" } else { "" };
    if !(-4..16).contains(&e) {
        let rest = if len == 1 { "0" } else { &ds[1..] };
        return format!("{sign}{}.{rest}e{e}", &ds[..1]);
    }
    if j >= 0 {
        return format!("{sign}{ds}{}.0", "0".repeat(j as usize));
    }
    let point = len + j;
    if point > 0 {
        format!("{sign}{}.{}", &ds[..point as usize], &ds[point as usize..])
    } else {
        format!("{sign}0.{}{ds}", "0".repeat((-point) as usize))
    }
}

fn hex_digits(e: u32, m: u32) -> u64 {
    (1 + u64::from(e) + u64::from(m)).div_ceil(4)
}

/// `0x` and the bits `b` of `float<e,m>` in hexadecimal.
fn hex_text(e: u32, m: u32, b: u128) -> String {
    format!("0x{b:0w$x}", w = hex_digits(e, m) as usize)
}

/// The one spelling of the bits `b` of `float<e,m>`, a format of at most
/// 128 bits.
pub fn spell_float(e: u32, m: u32, b: u128) -> String {
    if has_decimals(e, m) {
        let f = Format { e, m };
        if let Some(s) = f.decimal(b)
            && read_decimal(f, &s) == Some(b)
        {
            return s;
        }
    }
    hex_text(e, m, b)
}

/// The bits that the decimal `s` reads as, within the reader's bounds.
fn read_decimal(f: Format, s: &str) -> Option<u128> {
    let body = s.strip_prefix('-').unwrap_or(s);
    let (mantissa, exp) = match body.split_once('e') {
        Some((m, e)) => (m, e.parse::<i64>().ok()?),
        None => (body, 0),
    };
    let (whole, frac) = mantissa.split_once('.')?;
    if whole.len() > MAX_DIGITS || frac.len() > MAX_DIGITS || exp.abs() > MAX_EXP {
        return None;
    }
    let d = Big::from_digits(&format!("{whole}{frac}"));
    Some(f.read(s.starts_with('-'), &d, exp - frac.len() as i64))
}

/// The bits that the float literal `s` reads as at `float<e,m>`, a format
/// of at most 128 bits, before the check that `s` is their spelling
/// (`readFloatLit` in `lean/Fir/Core/FloatText.lean`).
pub fn read_float(e: u32, m: u32, s: &str) -> Option<u128> {
    if !is_float_lit(s) || 1 + u64::from(e) + u64::from(m) > 128 {
        return None;
    }
    if let Some(digits) = s.strip_prefix("0x") {
        let b = u128::from_str_radix(digits, 16).ok()?;
        let fits = digits.len() as u64 == hex_digits(e, m) && b >> (1 + e + m) == 0;
        return fits.then_some(b);
    }
    if !has_decimals(e, m) {
        return None;
    }
    read_decimal(Format { e, m }, s)
}

/// The bits that the float literal `s` spells at `float<e,m>`: `Ok(None)`
/// when it spells some, but the format is wider than 128 bits; and why
/// not, when it spells none.
pub fn float_constant(e: u32, m: u32, s: &str) -> Result<Option<u128>, String> {
    if !is_float_lit(s) {
        return Err(format!("{s} is not a float literal"));
    }
    let width = 1 + u64::from(e) + u64::from(m);
    if let Some(digits) = s.strip_prefix("0x") {
        let n = hex_digits(e, m);
        if digits.len() as u64 != n {
            return Err(format!(
                "the bits of a {width}-bit float are {n} hexadecimal digits"
            ));
        }
        let spare = (4 - width % 4) % 4;
        if u32::from_str_radix(&digits[..1], 16).expect("hexadecimal digits") >> (4 - spare) != 0 {
            return Err(format!("{s} does not fit {width} bits"));
        }
        if width > 128 {
            return Ok(None);
        }
        let b = u128::from_str_radix(digits, 16).expect("hexadecimal digits");
        return canonical(e, m, s, b);
    }
    if !has_decimals(e, m) {
        return Err(format!(
            "a float of {width} bits with {e} exponent bits has no decimals: write its bits after 0x"
        ));
    }
    let Some(b) = read_decimal(Format { e, m }, s) else {
        return Err(format!(
            "{s} has too many digits, or too large an exponent, to spell a float"
        ));
    };
    canonical(e, m, s, b)
}

fn canonical(e: u32, m: u32, s: &str, b: u128) -> Result<Option<u128>, String> {
    let spelling = spell_float(e, m, b);
    if spelling == s {
        Ok(Some(b))
    } else {
        Err(format!("{s} is written {spelling}"))
    }
}

#[cfg(test)]
mod tests;
