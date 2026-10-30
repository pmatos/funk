//! Squaring of polynomials by a number-theoretic transform over the prime
//! `P = 2^64 - 2^32 + 1`, in time `n log n`.
//!
//! `P - 1 = 2^32 (2^32 - 1)`, so the field has a root of unity of every
//! order `2^k` up to `2^32`, and `2^64 = 2^32 - 1 (mod P)` makes reduction a
//! few shifts and adds.

/// The prime `2^64 - 2^32 + 1`.
pub(super) const P: u64 = 0xFFFF_FFFF_0000_0001;

/// `2^64 - P`, so that `2^64 = EPS (mod P)`.
const EPS: u64 = 0xFFFF_FFFF;

/// A quadratic non-residue mod `P`, so that `7^((P - 1) / 2^k)` has order
/// exactly `2^k`.
const GENERATOR: u64 = 7;

/// The coefficients of `a(x)^2`, where `a` lists the coefficients of `a(x)`,
/// lowest first. They are exact only while each is below `P`; the caller
/// keeps them there.
pub(super) fn square(a: &[u64]) -> Vec<u64> {
    if a.is_empty() {
        return Vec::new();
    }
    let len = 2 * a.len() - 1;
    let n = len.next_power_of_two();
    let roots = roots(n);
    let mut f = a.to_vec();
    f.resize(n, 0);
    transform(&mut f, &roots);
    for x in &mut f {
        *x = mul(*x, *x);
    }
    // A second forward transform gives n times the coefficients, in the
    // order 0, n - 1, ..., 1.
    transform(&mut f, &roots);
    f[1..].reverse();
    f.truncate(len);
    let inv_n = pow(n as u64, P - 2);
    for x in &mut f {
        *x = mul(*x, inv_n);
    }
    f
}

/// The twiddle factors of every stage of a transform of length `n`: for
/// each power of two `h < n`, `roots[h + k]` is `w^k` for `k < h`, where `w`
/// has order `2h`.
fn roots(n: usize) -> Vec<u64> {
    let mut roots = vec![0; n];
    let half = n / 2;
    if half == 0 {
        return roots;
    }
    let w = pow(GENERATOR, (P - 1) / n as u64);
    let mut x = 1;
    for r in &mut roots[half..] {
        *r = x;
        x = mul(x, w);
    }
    for i in (1..half).rev() {
        roots[i] = roots[2 * i];
    }
    roots
}

/// The transform in place: `f[k]` becomes `sum_j f[j] w^(jk)`, where `w` has
/// order `f.len()`, a power of two.
fn transform(f: &mut [u64], roots: &[u64]) {
    let n = f.len();
    let mut j = 0;
    for i in 1..n {
        let mut bit = n >> 1;
        while j & bit != 0 {
            j ^= bit;
            bit >>= 1;
        }
        j |= bit;
        if i < j {
            f.swap(i, j);
        }
    }
    let mut half = 1;
    while half < n {
        let mut start = 0;
        while start < n {
            for k in 0..half {
                let u = f[start + k];
                let v = mul(f[start + half + k], roots[half + k]);
                f[start + k] = add(u, v);
                f[start + half + k] = sub(u, v);
            }
            start += 2 * half;
        }
        half *= 2;
    }
}

fn add(a: u64, b: u64) -> u64 {
    match a.overflowing_add(b) {
        // a + b - 2^64 + EPS = a + b - P, which is below P.
        (s, true) => s + EPS,
        (s, false) if s >= P => s - P,
        (s, false) => s,
    }
}

fn sub(a: u64, b: u64) -> u64 {
    if a >= b { a - b } else { P - (b - a) }
}

fn mul(a: u64, b: u64) -> u64 {
    reduce(u128::from(a) * u128::from(b))
}

/// `x mod P`, from `x = lo + hl 2^64 + hh 2^96 = lo + hl EPS - hh`, since
/// `2^96 = -1 (mod P)`.
fn reduce(x: u128) -> u64 {
    let lo = x as u64;
    let hi = (x >> 64) as u64;
    let (hh, hl) = (hi >> 32, hi & EPS);
    let t = match lo.overflowing_sub(hh) {
        // The wrapped value is 2^64 = EPS too much, and at least 2^64 - 2^32.
        (t, true) => t - EPS,
        (t, false) => t,
    };
    let s = match t.overflowing_add(hl * EPS) {
        (s, true) => s + EPS,
        (s, false) => s,
    };
    if s >= P { s - P } else { s }
}

fn pow(mut base: u64, mut exp: u64) -> u64 {
    let mut acc = 1;
    while exp > 0 {
        if exp & 1 == 1 {
            acc = mul(acc, base);
        }
        base = mul(base, base);
        exp >>= 1;
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::generate::Rng;

    const EDGES: [u64; 9] = [0, 1, 2, EPS, EPS + 1, P / 2, P - 2, P - 1, 1 << 63];

    #[test]
    fn the_generator_gives_roots_of_every_order_up_to_2_pow_32() {
        assert_eq!(pow(GENERATOR, (P - 1) / 2), P - 1);
        let w = pow(GENERATOR, (P - 1) >> 32);
        assert_eq!(pow(w, 1 << 31), P - 1);
        assert_eq!(pow(w, 1 << 32), 1);
    }

    #[test]
    fn field_operations_agree_with_u128_arithmetic() {
        let p = u128::from(P);
        let mut rng = Rng::new(37);
        let mut values = EDGES.to_vec();
        values.extend((0..200).map(|_| rng.next_u64() % P));
        for &a in &values {
            for &b in &values {
                let (wa, wb) = (u128::from(a), u128::from(b));
                assert_eq!(u128::from(add(a, b)), (wa + wb) % p, "{a} + {b}");
                assert_eq!(u128::from(sub(a, b)), (wa + p - wb) % p, "{a} - {b}");
                assert_eq!(u128::from(mul(a, b)), wa * wb % p, "{a} * {b}");
            }
        }
        for _ in 0..10_000 {
            let x = (u128::from(rng.next_u64()) << 64) | u128::from(rng.next_u64());
            assert_eq!(u128::from(reduce(x)), x % p, "{x}");
        }
        assert_eq!(reduce(u128::MAX), (u128::MAX % p) as u64);
    }

    #[test]
    fn squares_agree_with_the_schoolbook_product() {
        let mut rng = Rng::new(5);
        let mut lens: Vec<usize> = (0..70).collect();
        lens.extend((0..30).map(|_| 70 + rng.below(500) as usize));
        for len in lens {
            let bound = [2, 100_000, 1 << 24][rng.below(3) as usize];
            let a: Vec<u64> = (0..len).map(|_| rng.below(bound)).collect();
            let mut expected = vec![0u64; (2 * len).saturating_sub(1)];
            for (i, x) in a.iter().enumerate() {
                for (j, y) in a.iter().enumerate() {
                    expected[i + j] += x * y;
                }
            }
            assert_eq!(square(&a), expected, "length {len}");
        }
    }
}
