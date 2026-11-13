//! `fpext` from `f32` to `f64` and `fptrunc` from `f64` to `f32` run
//! natively (#241,
//! `docs/decisions/x86-64-backend-lowering.md#conversions-between-formats`).
//! Each result is checked against the host's own conversion, Rust's `as`,
//! which is exact from `f32` to `f64` and rounds to nearest, ties to even,
//! from `f64` to `f32`, with an infinity past the largest finite value and a
//! zero of its sign below half the smallest subnormal, as `round(rne)`
//! asks. A NaN gives any NaN (ADR-2026-11-09-1549), so a NaN's result is
//! checked only to be a NaN.
//!
//! The cases are the zeros, the subnormals and normals at each edge, the
//! largest finite values, the infinities and NaNs of either sign, the
//! values halfway between two `f32` values and next to them, the edges of
//! overflow and underflow, and random bits. Each operand is a `bitcast` of
//! an integer constant, so any bit pattern is a case, and each batch is
//! one function that returns every result, so one build and one run check
//! many cases.

mod common;

use common::{build, func, module, run, text};

/// A small generator of random bits, so that every run checks the same
/// values.
struct Bits(u64);

impl Bits {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }
}

/// The cases of `f32`, as bits.
fn f32_cases(bits: &mut Bits) -> Vec<u64> {
    let mut out: Vec<u64> = vec![
        0,
        1,
        2,
        0x007f_ffff,
        0x0080_0000,
        0x0080_0001,
        0x3f80_0000,
        0x3dcc_cccd,
        0x7f7f_ffff,
        0x7f80_0000,
        0x7f80_0001,
        0x7fc0_0000,
        0x7fff_ffff,
    ];
    out.extend(out.clone().into_iter().map(|b| b | 0x8000_0000));
    out.extend((0..64).map(|_| bits.next() & 0xffff_ffff));
    out
}

/// The cases of `f64`, as bits: as for `f32`, and the edges of each
/// rounding into `f32`.
fn f64_cases(bits: &mut Bits) -> Vec<u64> {
    let f = |x: f64| x.to_bits();
    let ulp32 = 2f64.powi(-23);
    let tiny = 2f64.powi(-149);
    let big = f64::from(f32::MAX);
    let big_half = 2f64.powi(103);
    let mut out: Vec<u64> = vec![
        0,
        1,
        0x000f_ffff_ffff_ffff,
        0x0010_0000_0000_0000,
        0x7fef_ffff_ffff_ffff,
        0x7ff0_0000_0000_0000,
        0x7ff0_0000_0000_0001,
        0x7ff8_0000_0000_0000,
        0x7fff_ffff_ffff_ffff,
        f(1.0),
        f(0.1),
        // Halfway between 1 and the next `f32`, which goes to 1; three
        // halves of an ulp, which goes up; and their neighbours.
        f(1.0 + ulp32 / 2.0),
        f(1.0 + ulp32 / 2.0) + 1,
        f(1.0 + ulp32 / 2.0) - 1,
        f(1.0 + 3.0 * ulp32 / 2.0),
        // The largest finite `f32`, halfway past it, which is an infinity,
        // and just below that, which is not.
        f(big),
        f(big + big_half),
        f(big + big_half) - 1,
        f(big + 2.0 * big_half),
        // The smallest subnormal `f32`, half of it, which goes to zero, and
        // just above half, which goes up; a subnormal halfway case.
        f(tiny),
        f(tiny / 2.0),
        f(tiny / 2.0) + 1,
        f(tiny / 4.0),
        f(tiny * 2.5),
        f(tiny * 3.5),
        // The smallest normal `f32`, and the largest subnormal plus half.
        f(2f64.powi(-126)),
        f(2f64.powi(-126) - tiny / 2.0),
    ];
    out.extend(out.clone().into_iter().map(|b| b | 1 << 63));
    out.extend((0..64).map(|_| bits.next()));
    // Random values in `f32`'s range, whose low bits round.
    out.extend((0..64).map(|_| {
        let b = bits.next();
        let exp = 0x380 + (b >> 52) % 0xff;
        (b & 0x800f_ffff_ffff_ffff) | exp << 52
    }));
    out
}

/// The host's conversion of `b` from `from` to `to`.
fn host(from: &str, b: u64) -> u64 {
    if from == "f32" {
        (f64::from(f32::from_bits(b as u32))).to_bits()
    } else {
        u64::from((f64::from_bits(b) as f32).to_bits())
    }
}

/// Whether the bits `b` of `ty` are a NaN.
fn is_nan(ty: &str, b: u64) -> bool {
    if ty == "f32" {
        f32::from_bits(b as u32).is_nan()
    } else {
        f64::from_bits(b).is_nan()
    }
}

/// Converts each case with `op` from `from` to `to` natively, in batches
/// of 64, and checks each result against the host.
fn check(op: &str, from: &str, to: &str, cases: &[u64]) {
    let (bits, attr) = if from == "f32" {
        ("i32", "")
    } else {
        ("i64", " round(rne)")
    };
    let mut funcs = Vec::new();
    let mut batches = Vec::new();
    for (n, batch) in cases.chunks(64).enumerate() {
        let mut body = Vec::new();
        let mut results = Vec::new();
        for (i, &b) in batch.iter().enumerate() {
            let c = if from == "f32" {
                i64::from(b as u32 as i32)
            } else {
                b as i64
            };
            body.push(format!("%b{i}: {bits} = const {c}"));
            body.push(format!("%c{i}: {from} = bitcast %b{i}"));
            body.push(format!("%r{i}: {to} = {op}{attr} %c{i}"));
            results.push(format!("%r{i}"));
        }
        body.push(format!("ret {}", results.join(", ")));
        let body: Vec<&str> = body.iter().map(String::as_str).collect();
        let types = vec![to; batch.len()].join(", ");
        let name = format!("b{n}");
        funcs.push(func(&name, "", &types, &body));
        batches.push((name, batch.to_vec()));
    }
    let exe = build(op, &module(&funcs));
    let mask = if to == "f32" { 0xffff_ffff } else { u64::MAX };
    for (name, batch) in batches {
        let out = run(&exe, &[&format!("@{name}")]);
        let stdout = text(&out.stdout);
        assert_eq!(out.status.code(), Some(0), "{stdout}{}", text(&out.stderr));
        let got: Vec<u64> = stdout
            .trim_end()
            .strip_prefix("{\"values\":[")
            .and_then(|s| s.strip_suffix("]}"))
            .expect("a JSON line of values")
            .split(',')
            .map(|v| v.trim_matches('"').parse::<i64>().expect("a float's bits") as u64 & mask)
            .collect();
        assert_eq!(got.len(), batch.len(), "{stdout}");
        for (&b, &g) in batch.iter().zip(&got) {
            if is_nan(from, b) {
                assert!(
                    is_nan(to, g),
                    "{op} of {from} {b:#x} gave {g:#x}, not a NaN"
                );
            } else {
                assert_eq!(g, host(from, b), "{op} of {from} {b:#x} to {to}");
            }
        }
    }
}

#[test]
fn fpext_from_f32_to_f64_is_exact() {
    check("fpext", "f32", "f64", &f32_cases(&mut Bits(0x2412)));
}

#[test]
fn fptrunc_from_f64_to_f32_rounds_as_the_host_does() {
    check("fptrunc", "f64", "f32", &f64_cases(&mut Bits(0x2412)));
}

/// The host rounds the edges as `round(rne)` asks, so the cases check what
/// they say.
#[test]
fn the_host_rounds_the_edges_to_nearest_even() {
    let f = |x: f64| x.to_bits();
    let ulp32 = 2f64.powi(-23);
    let tiny = 2f64.powi(-149);
    assert_eq!(host("f64", f(1.0 + ulp32 / 2.0)), 0x3f80_0000);
    assert_eq!(host("f64", f(1.0 + 3.0 * ulp32 / 2.0)), 0x3f80_0002);
    assert_eq!(host("f64", f(tiny / 2.0)), 0);
    assert_eq!(host("f64", f(tiny / 2.0) + 1), 1);
    assert_eq!(host("f64", f(-tiny / 2.0)), 0x8000_0000);
    let past = f(f64::from(f32::MAX) + 2f64.powi(103));
    assert_eq!(host("f64", past), 0x7f80_0000);
    assert_eq!(host("f64", past - 1), 0x7f7f_ffff);
    assert_eq!(host("f32", 1), f(tiny));
}
