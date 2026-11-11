//! The unsigned integers of any size that reading and spelling a float
//! constant compute with: products by powers of two and ten, comparisons,
//! differences and quotients that fit a `u128` or a few hundred bits.

use std::cmp::Ordering;

/// An unsigned integer, as little-endian 32-bit limbs with no high zero
/// limb.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Big(Vec<u32>);

impl Big {
    pub(super) fn zero() -> Big {
        Big(Vec::new())
    }

    pub(super) fn from_u128(mut v: u128) -> Big {
        let mut limbs = Vec::new();
        while v != 0 {
            limbs.push(v as u32);
            v >>= 32;
        }
        Big(limbs)
    }

    /// The value of the decimal digits `ds`.
    pub(super) fn from_digits(ds: &str) -> Big {
        let mut n = Big::zero();
        for chunk in ds.as_bytes().chunks(9) {
            let value = chunk.iter().fold(0u32, |a, d| a * 10 + u32::from(d - b'0'));
            n.mul_add_small(10u32.pow(chunk.len() as u32), value);
        }
        n
    }

    pub(super) fn is_zero(&self) -> bool {
        self.0.is_empty()
    }

    /// The value, when it fits a `u128`.
    pub(super) fn to_u128(&self) -> Option<u128> {
        if self.0.len() > 4 {
            return None;
        }
        Some(
            self.0
                .iter()
                .rev()
                .fold(0u128, |a, &l| (a << 32) | u128::from(l)),
        )
    }

    /// The number of bits needed to write the value; 0 for zero.
    pub(super) fn bit_len(&self) -> u64 {
        match self.0.last() {
            None => 0,
            Some(top) => 32 * (self.0.len() as u64 - 1) + u64::from(32 - top.leading_zeros()),
        }
    }

    fn trim(mut self) -> Big {
        while self.0.last() == Some(&0) {
            self.0.pop();
        }
        self
    }

    fn mul_add_small(&mut self, m: u32, a: u32) {
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

    /// `self · 10^k`.
    pub(super) fn mul_pow10(&self, mut k: u64) -> Big {
        let mut n = self.clone();
        while k >= 9 {
            n.mul_add_small(1_000_000_000, 0);
            k -= 9;
        }
        n.mul_add_small(10u32.pow(k as u32), 0);
        n.trim()
    }

    /// `self · 2^k`.
    pub(super) fn shl(&self, k: u64) -> Big {
        if self.is_zero() {
            return Big::zero();
        }
        let (limbs, bits) = ((k / 32) as usize, (k % 32) as u32);
        let mut out = vec![0u32; limbs];
        let mut carry = 0u32;
        for &l in &self.0 {
            out.push(if bits == 0 { l } else { (l << bits) | carry });
            carry = if bits == 0 { 0 } else { l >> (32 - bits) };
        }
        out.push(carry);
        Big(out).trim()
    }

    /// `self - other`, for `other <= self`.
    pub(super) fn sub(&self, other: &Big) -> Big {
        let mut out = self.0.clone();
        let mut borrow = 0i64;
        for (i, limb) in out.iter_mut().enumerate() {
            let v = i64::from(*limb) - i64::from(other.0.get(i).copied().unwrap_or(0)) - borrow;
            borrow = i64::from(v < 0);
            *limb = (v + (borrow << 32)) as u32;
        }
        Big(out).trim()
    }

    pub(super) fn add(&self, other: &Big) -> Big {
        let mut out = Vec::with_capacity(self.0.len().max(other.0.len()) + 1);
        let mut carry = 0u64;
        for i in 0..self.0.len().max(other.0.len()) {
            let v = u64::from(self.0.get(i).copied().unwrap_or(0))
                + u64::from(other.0.get(i).copied().unwrap_or(0))
                + carry;
            out.push(v as u32);
            carry = v >> 32;
        }
        out.push(carry as u32);
        Big(out).trim()
    }

    /// `self · other`, limb by limb.
    pub(super) fn mul(&self, other: &Big) -> Big {
        let mut out = vec![0u32; self.0.len() + other.0.len() + 1];
        for (i, &a) in self.0.iter().enumerate() {
            let mut carry = 0u64;
            for (j, &b) in other.0.iter().enumerate() {
                let v = u64::from(out[i + j]) + u64::from(a) * u64::from(b) + carry;
                out[i + j] = v as u32;
                carry = v >> 32;
            }
            let mut k = i + other.0.len();
            while carry != 0 {
                let v = u64::from(out[k]) + carry;
                out[k] = v as u32;
                carry = v >> 32;
                k += 1;
            }
        }
        Big(out).trim()
    }

    /// `(self / d, self % d)` by long division, one quotient bit at a time:
    /// the quotients that reading and spelling take are short.
    pub(super) fn div_rem(&self, d: &Big) -> (Big, Big) {
        let mut q = Big::zero();
        let mut r = self.clone();
        if r.cmp(d) == Ordering::Less {
            return (q, r);
        }
        let mut shift = r.bit_len() - d.bit_len();
        loop {
            let ds = d.shl(shift);
            if r.cmp(&ds) != Ordering::Less {
                r = r.sub(&ds);
                q = q.add(&Big::from_u128(1).shl(shift));
            }
            if shift == 0 {
                return (q, r);
            }
            shift -= 1;
        }
    }

    pub(super) fn is_even(&self) -> bool {
        self.0.first().is_none_or(|l| l % 2 == 0)
    }

    /// The decimal digits of the value, with no leading zeros.
    pub(super) fn to_digits(&self) -> String {
        let mut n = self.clone();
        let mut chunks = Vec::new();
        while !n.is_zero() {
            let mut rem = 0u64;
            for limb in n.0.iter_mut().rev() {
                let v = (rem << 32) | u64::from(*limb);
                *limb = (v / 1_000_000_000) as u32;
                rem = v % 1_000_000_000;
            }
            n = n.trim();
            chunks.push(rem);
        }
        let mut out = chunks
            .pop()
            .map_or_else(|| "0".to_string(), |c| c.to_string());
        for c in chunks.iter().rev() {
            out.push_str(&format!("{c:09}"));
        }
        out
    }
}

impl PartialOrd for Big {
    fn partial_cmp(&self, other: &Big) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Big {
    fn cmp(&self, other: &Big) -> Ordering {
        self.0
            .len()
            .cmp(&other.0.len())
            .then_with(|| self.0.iter().rev().cmp(other.0.iter().rev()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn arithmetic_agrees_with_u128() {
        let a = Big::from_u128(123_456_789_012_345_678_901_234_567);
        let b = Big::from_u128(987_654_321);
        assert_eq!(
            a.add(&b).to_u128(),
            Some(123_456_789_012_345_679_888_888_888)
        );
        assert_eq!(
            a.sub(&b).to_u128(),
            Some(123_456_789_012_345_677_913_580_246)
        );
        let (q, r) = a.div_rem(&b);
        assert_eq!(
            q.to_u128(),
            Some(123_456_789_012_345_678_901_234_567 / 987_654_321)
        );
        assert_eq!(
            r.to_u128(),
            Some(123_456_789_012_345_678_901_234_567 % 987_654_321)
        );
        assert_eq!(b.shl(40).to_u128(), Some(987_654_321u128 << 40));
        assert_eq!(b.mul(&b).to_u128(), Some(987_654_321u128 * 987_654_321));
        assert_eq!(a.mul(&Big::zero()), Big::zero());
        assert_eq!(b.mul_pow10(20).to_digits(), "98765432100000000000000000000");
        assert_eq!(Big::from_digits("000123").to_u128(), Some(123));
        assert_eq!(Big::zero().to_digits(), "0");
        assert!(a > b && Big::from_u128(4).is_even() && !b.is_even());
    }
}
