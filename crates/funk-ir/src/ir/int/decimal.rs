//! Powers of two in decimal, in time `n log n`, so that a constant of
//! millions of digits is checked against its width without converting it
//! to binary (#37).

use std::cell::RefCell;
use std::cmp::Ordering;

use super::ntt;

thread_local! {
    /// The last power of two built, with its exponent: a module's constants
    /// near a limit mostly share a width, and `funk verify` checks each twice.
    static LAST_POW2: RefCell<Option<(u64, Vec<u64>)>> = const { RefCell::new(None) };
}

/// The limbs are base-10^5 digits. A square of `n` limbs then has
/// coefficients below `n 10^10`, under the transform's prime for every `n`
/// below 1.8 billion: every power `2^k` with `k < 2^32` stays well inside.
const BASE: u64 = 100_000;
const BASE_DIGITS: usize = 5;

/// How the value of `digits`, a canonical decimal spelling, compares with
/// `2^k`.
pub(super) fn cmp_pow2(digits: &str, k: u64) -> Ordering {
    LAST_POW2.with_borrow_mut(|last| {
        let p = match last.take() {
            Some((at, p)) if at == k => p,
            _ => pow2(k),
        };
        // With no leading zero, the top limb of `digits` is not zero, except
        // in "0", which is below every power anyway.
        let v = digits.as_bytes().rchunks(BASE_DIGITS);
        let order = v.len().cmp(&p.len()).then_with(|| {
            v.rev()
                .map(|chunk| chunk.iter().fold(0, |a, d| a * 10 + u64::from(d - b'0')))
                .cmp(p.iter().rev().copied())
        });
        *last = Some((k, p));
        order
    })
}

/// `2^k` as base-10^5 limbs, lowest first, by squaring and doubling along
/// the bits of `k`.
fn pow2(k: u64) -> Vec<u64> {
    let mut x = vec![1];
    for bit in (0..u64::BITS - k.leading_zeros()).rev() {
        x = square(&x);
        if (k >> bit) & 1 == 1 {
            x.iter_mut().for_each(|l| *l *= 2);
            x = carry(x);
        }
    }
    x
}

fn square(x: &[u64]) -> Vec<u64> {
    let largest = u128::from((BASE - 1) * (BASE - 1));
    assert!(
        x.len() as u128 * largest < u128::from(ntt::P),
        "{} limbs are too many to square exactly",
        x.len()
    );
    carry(ntt::square(x))
}

/// Base-10^5 limbs from coefficients that may exceed the base.
fn carry(mut coefficients: Vec<u64>) -> Vec<u64> {
    let mut carry = 0;
    for c in &mut coefficients {
        let v = *c + carry;
        *c = v % BASE;
        carry = v / BASE;
    }
    while carry != 0 {
        coefficients.push(carry % BASE);
        carry /= BASE;
    }
    while coefficients.last() == Some(&0) {
        coefficients.pop();
    }
    coefficients
}

/// The decimal digits of `2^k`.
#[cfg(test)]
pub(super) fn pow2_digits(k: u64) -> String {
    use std::fmt::Write;

    let limbs = pow2(k);
    let (top, rest) = limbs.split_last().expect("2^k is not zero");
    let mut out = top.to_string();
    for limb in rest.iter().rev() {
        write!(out, "{limb:05}").expect("writing to a String does not fail");
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::generate::Rng;
    use crate::ir::Nat;

    #[test]
    fn powers_of_two_agree_with_the_schoolbook_conversion() {
        let mut rng = Rng::new(10);
        let ks = (0..=300).chain((0..40).map(|_| rng.below(40_000)));
        for k in ks {
            assert_eq!(pow2_digits(k), Nat::pow2(k).to_decimal(), "2^{k}");
        }
    }

    #[test]
    fn digit_strings_compare_with_powers_of_two() {
        assert_eq!(cmp_pow2("0", 0), Ordering::Less);
        assert_eq!(cmp_pow2("1", 0), Ordering::Equal);
        assert_eq!(cmp_pow2("2", 0), Ordering::Greater);
        assert_eq!(cmp_pow2("0", 70), Ordering::Less);
        let edge = 1u128 << 100;
        for (v, order) in [
            (edge - 1, Ordering::Less),
            (edge, Ordering::Equal),
            (edge + 1, Ordering::Greater),
            (edge / 10, Ordering::Less),
            (edge * 10, Ordering::Greater),
        ] {
            assert_eq!(cmp_pow2(&v.to_string(), 100), order, "{v}");
        }
    }
}
