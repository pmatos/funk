//! Division at `i128` (#22): `sdiv` and `udiv`, each with and without
//! `exact`, `srem` and `urem`, run natively through the runtime helper
//! (ADR-2026-11-03-0414, ADR-2026-11-03-0415) and checked against Rust's
//! `i128` and `u128` arithmetic. The values cross `2^63` and `2^64`, take
//! both signs, and take each path of the helper: a divisor below `2^64`,
//! with a dividend whose high half is below it or not, and a divisor of
//! `2^64` or more, near its multiples. A run whose source is UB, a zero
//! divisor or `sdiv` and `srem` of the signed minimum by `-1`, is not
//! made: natively it may trap. Where a broken `exact` gives poison, a run
//! asks only for a value of the type (ADR-2026-10-30-2248).

mod common;

use std::path::Path;

use common::{build, check_i128, func, module};

/// The functions of the module: each op, and what it computes, or `None`
/// where the source is UB or poison. `exact` and the run's UB are left to
/// [`result`].
type Op = (&'static str, &'static str, fn(i128, i128) -> Option<i128>);

const OPS: [Op; 6] = [
    ("sdiv", "sdiv", |a, b| a.checked_div(b)),
    ("sdiv_exact", "sdiv exact", |a, b| a.checked_div(b)),
    ("udiv", "udiv", |a, b| unsigned(a, b, u128::checked_div)),
    ("udiv_exact", "udiv exact", |a, b| {
        unsigned(a, b, u128::checked_div)
    }),
    ("srem", "srem", |a, b| a.checked_rem(b)),
    ("urem", "urem", |a, b| unsigned(a, b, u128::checked_rem)),
];

/// `f` of `a` and `b` read as unsigned, as a value of `i128`.
fn unsigned(a: i128, b: i128, f: fn(u128, u128) -> Option<u128>) -> Option<i128> {
    f(a as u128, b as u128).map(|r| r as i128)
}

/// Whether the source is UB on `a` and `b`: a zero divisor, or `sdiv` and
/// `srem` of the signed minimum by `-1`.
fn ub(name: &str, a: i128, b: i128) -> bool {
    b == 0 || (name.starts_with('s') && a == i128::MIN && b == -1)
}

/// What `name` gives on `a` and `b`, which are not UB: the exact result,
/// or `None` where `exact` is broken, so that the result is poison.
fn result(name: &str, f: fn(i128, i128) -> Option<i128>, a: i128, b: i128) -> Option<i128> {
    let q = f(a, b).expect("not UB");
    let exact = match name {
        "sdiv_exact" => a.checked_rem(b) == Some(0),
        "udiv_exact" => (a as u128).is_multiple_of(b as u128),
        _ => true,
    };
    exact.then_some(q)
}

/// The executable of the six functions.
fn executable(name: &str) -> std::path::PathBuf {
    let funcs: Vec<String> = OPS
        .iter()
        .map(|(f, op, _)| {
            let line = format!("%r: i128 = {op} %a, %b");
            func(f, "%a: i128, %b: i128", "i128", &[&line, "ret %r"])
        })
        .collect();
    build(name, &module(&funcs))
}

/// Runs each op on each pair of `pairs` that is not UB, and returns how
/// many runs gave poison.
fn run_pairs(exe: &Path, pairs: &[(i128, i128)]) -> usize {
    let mut poison = 0;
    for &(a, b) in pairs {
        let (sa, sb) = (a.to_string(), b.to_string());
        for (name, _, f) in OPS {
            if ub(name, a, b) {
                continue;
            }
            let r = result(name, f, a, b);
            poison += usize::from(r.is_none());
            check_i128(exe, &[&format!("@{name}"), &sa, &sb], r);
        }
    }
    poison
}

/// The boundary bit patterns, values on either side of `2^63`, `2^64` and
/// `2^127` and their negations, small divisors of both signs, and values
/// whose halves differ.
const VALUES: [i128; 22] = [
    0,
    1,
    -1,
    2,
    7,
    -7,
    i128::MIN,
    i128::MIN + 1,
    i128::MAX,
    (1 << 63) - 1,
    1 << 63,
    -(1 << 63),
    (1 << 64) - 1,
    1 << 64,
    (1 << 64) + 1,
    -(1 << 64),
    -(1 << 64) - 1,
    3 << 64,
    (1 << 100) + 12345,
    -(1 << 100) - 12345,
    0x0123_4567_89ab_cdef_fedc_ba98_7654_3210,
    -0x0123_4567_89ab_cdef_fedc_ba98_7654_3210,
];

fn all_pairs(values: &[i128]) -> Vec<(i128, i128)> {
    let mut out = Vec::new();
    for &a in values {
        for &b in values {
            out.push((a, b));
        }
    }
    out
}

#[test]
fn every_pair_of_values_divides_as_rust_does() {
    let exe = executable("i128-div-values");
    let poison = run_pairs(&exe, &all_pairs(&VALUES));
    assert!(poison > 0, "no division leaves a remainder under exact");
}

/// A divisor below `2^64` takes two `divq`; the first leaves a remainder
/// of the dividend's high half, zero or not, that the second divides with
/// the low half. A dividend whose high half is below the divisor gives a
/// quotient whose high half is 0, and one at or above it a quotient wider
/// than 64 bits.
#[test]
fn divisors_below_2_to_the_64_divide_by_one_digit() {
    let exe = executable("i128-div-narrow");
    let divisors: [i128; 8] = [
        1,
        3,
        10,
        0xffff_ffff,
        (1 << 63) - 25,
        1 << 63,
        (1 << 64) - 59,
        (1 << 64) - 1,
    ];
    let mut pairs = Vec::new();
    for b in divisors {
        for a in [
            b - 1,
            b,
            b + 1,
            (b << 32) + 17,
            (b << 63) | 5,
            b.wrapping_mul(b),
            b.wrapping_mul(b).wrapping_sub(1),
            ((b - 1) << 64) | ((1 << 64) - 1),
            ((1 << 64) - 1) << 64,
            i128::MAX,
            i128::MIN,
            -1,
        ] {
            pairs.extend([(a, b), (a, -b)]);
        }
    }
    run_pairs(&exe, &pairs);
}

/// A divisor of `2^64` or more takes the restoring division, whose
/// quotient fits in 64 bits: dividends near its multiples set each bit of
/// the quotient or leave it clear, and a divisor of `2^127` or more, read
/// as unsigned, gives a quotient of 0 or 1.
#[test]
fn divisors_of_2_to_the_64_or_more_divide_bit_by_bit() {
    let exe = executable("i128-div-wide");
    let divisors: [i128; 8] = [
        1 << 64,
        (1 << 64) + 1,
        (5 << 64) + 3,
        0x0000_0001_ffff_ffff_ffff_ffff_ffff_ffff,
        (1 << 126) + (1 << 70) + 99,
        i128::MAX,
        i128::MIN + 1,
        -(1 << 64) - 7,
    ];
    let mut pairs = Vec::new();
    for b in divisors {
        let u = b as u128;
        let mut near = vec![u - 1, u, u + 1, u.wrapping_mul(2)];
        for k in [2u128, 3, 0xffff, 1 << 40, (1 << 63) + 1] {
            if let Some(m) = u.checked_mul(k) {
                near.extend([m - 1, m, m.wrapping_add(1), m.wrapping_add(u - 1)]);
            }
        }
        near.extend([u128::MAX, u128::MAX - 1, 1 << 127, (1 << 127) - 1, 0, 1]);
        for a in near {
            pairs.push((a as i128, b));
            pairs.push((a as i128, b.wrapping_neg()));
        }
    }
    run_pairs(&exe, &pairs);
}

/// Pairs from a fixed sequence of xorshift values, each cut to a random
/// number of bits and given a random sign.
#[test]
fn pseudo_random_pairs_divide_as_rust_does() {
    let exe = executable("i128-div-random");
    let mut state = 0x2545_f491_4f6c_dd1d_u64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let mut value = || {
        let v = (u128::from(next()) << 64) | u128::from(next());
        let bits = next() % 128 + 1;
        let v = (v >> (128 - bits)) as i128;
        if next() % 2 == 0 { v } else { v.wrapping_neg() }
    };
    let pairs: Vec<(i128, i128)> = (0..300).map(|_| (value(), value())).collect();
    run_pairs(&exe, &pairs);
}
