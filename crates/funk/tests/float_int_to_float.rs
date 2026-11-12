//! `sitofp` and `uitofp` run natively from `i1`, `i8`, `i16`, `i32`, `i64`
//! and `i128` to `f32` and `f64` (#241,
//! `docs/decisions/x86-64-backend-lowering.md#conversions-from-integers`).
//! Each result is checked against the host's own conversion, Rust's `as`,
//! which rounds to nearest, ties to even, and gives an infinity past the
//! largest finite value, as `round(rne)` asks.
//!
//! The cases are the boundary values of each width, the powers of two and
//! their neighbours, the integers halfway between two floats of each
//! format, just above and below them, and random values. An operand
//! narrower than 64 bits is the `trunc` of an `i64` whose high bits are
//! random, so the conversion must read only the operand's own bits.
//!
//! Each batch is one function that converts constants and returns every
//! result, so one build and one run check many cases.

mod common;

use common::{build, func, module, run, text};

/// The widths the backend lowers.
const WIDTHS: [u32; 6] = [1, 8, 16, 32, 64, 128];

/// A float format the backend lowers: its name, its width and its
/// precision, the bits of its mantissa with the hidden one.
#[derive(Clone, Copy)]
struct Format {
    name: &'static str,
    bits: u32,
    precision: u32,
}

const F32: Format = Format {
    name: "f32",
    bits: 32,
    precision: 24,
};

const F64: Format = Format {
    name: "f64",
    bits: 64,
    precision: 53,
};

/// The host's conversion of the bits `v` of `iW` to `f`, read as signed
/// when `signed`.
fn host(f: Format, w: u32, v: u128, signed: bool) -> u64 {
    let x: i128 = if signed {
        ((v << (128 - w)) as i128) >> (128 - w)
    } else {
        0
    };
    let u: u128 = (v << (128 - w)) >> (128 - w);
    match (f.bits, signed) {
        (32, true) => u64::from((x as f32).to_bits()),
        (32, false) => u64::from((u as f32).to_bits()),
        (_, true) => (x as f64).to_bits(),
        (_, false) => (u as f64).to_bits(),
    }
}

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

    fn wide(&mut self) -> u128 {
        (u128::from(self.next()) << 64) | u128::from(self.next())
    }
}

/// The cases of `iW`, as bits: the boundary values, each power of two that
/// matters to `f32` or `f64` with its neighbours, the integers halfway
/// between two floats of either format near it and next to them, and
/// random values.
fn cases(w: u32, bits: &mut Bits) -> Vec<u128> {
    let mask = u128::MAX >> (128 - w);
    let top = mask >> 1;
    let mut out = vec![0, 1, mask, top, top + 1, top.wrapping_sub(1)];
    for k in [
        1, 7, 15, 23, 24, 25, 31, 52, 53, 54, 62, 63, 64, 100, 126, 127,
    ] {
        if k >= w {
            continue;
        }
        let p = 1u128 << k;
        out.extend([p, p - 1, p + 1, (p << 1).wrapping_sub(1)]);
        for precision in [F32.precision, F64.precision] {
            if k >= precision {
                // Halfway between 2^k and the next float, and just above.
                let half = 1u128 << (k - precision);
                out.extend([p + half, p + half + 1, p + 3 * half, p + half - 1]);
            }
        }
    }
    for _ in 0..16 {
        out.push(bits.wide());
    }
    let mut out: Vec<u128> = out.into_iter().map(|v| v & mask).collect();
    out.sort_unstable();
    out.dedup();
    out
}

/// The text of an operand of `iW` with the bits `v`: a constant, or below
/// 64 bits the `trunc` of an `i64` constant whose bits above `W` are
/// `high`'s.
fn operand(name: &str, w: u32, v: u128, high: u64, body: &mut Vec<String>) {
    match w {
        128 => body.push(format!("%{name}: i128 = const {}", v as i128)),
        64 => body.push(format!("%{name}: i64 = const {}", v as u64 as i64)),
        _ => {
            let wide = (high << w) | v as u64;
            body.push(format!("%{name}h: i64 = const {}", wide as i64));
            body.push(format!("%{name}: i{w} = trunc %{name}h"));
        }
    }
}

/// Converts each case of `iW` to `f` with `op` natively, in batches of 64,
/// and checks each result against the host.
fn check(f: Format, op: &str) {
    let signed = op == "sitofp";
    let mut bits = Bits(0x2401);
    let mut funcs = Vec::new();
    let mut batches = Vec::new();
    for w in WIDTHS {
        for (n, batch) in cases(w, &mut bits).chunks(64).enumerate() {
            let mut body = Vec::new();
            let mut results = Vec::new();
            for (i, &v) in batch.iter().enumerate() {
                operand(&format!("c{i}"), w, v, bits.next(), &mut body);
                body.push(format!("%r{i}: {} = {op} round(rne) %c{i}", f.name));
                results.push(format!("%r{i}"));
            }
            body.push(format!("ret {}", results.join(", ")));
            let body: Vec<&str> = body.iter().map(String::as_str).collect();
            let types = vec![f.name; batch.len()].join(", ");
            let name = format!("i{w}_{n}");
            funcs.push(func(&name, "", &types, &body));
            batches.push((name, w, batch.to_vec()));
        }
    }
    let exe = build(&format!("{op}-{}", f.name), &module(&funcs));
    for (name, w, batch) in batches {
        let out = run(&exe, &[&format!("@{name}")]);
        let stdout = text(&out.stdout);
        assert_eq!(out.status.code(), Some(0), "{stdout}{}", text(&out.stderr));
        let got: Vec<u64> = stdout
            .trim_end()
            .strip_prefix("{\"values\":[")
            .and_then(|s| s.strip_suffix("]}"))
            .expect("a JSON line of values")
            .split(',')
            .map(|v| v.trim_matches('"').parse::<i64>().expect("a float's bits") as u64)
            .collect();
        let mask = u64::MAX >> (64 - f.bits);
        for (&v, &g) in batch.iter().zip(&got) {
            let want = host(f, w, v, signed);
            assert_eq!(g & mask, want, "{op} of i{w} {v:#x} to {}", f.name);
        }
    }
}

#[test]
fn sitofp_to_f32_rounds_as_the_host_does() {
    check(F32, "sitofp");
}

#[test]
fn sitofp_to_f64_rounds_as_the_host_does() {
    check(F64, "sitofp");
}

#[test]
fn uitofp_to_f32_rounds_as_the_host_does() {
    check(F32, "uitofp");
}

#[test]
fn uitofp_to_f64_rounds_as_the_host_does() {
    check(F64, "uitofp");
}

/// The cases include the edges that the lowering takes apart: an unsigned
/// `i64` of `2^63` or more, an `i128` with bits only in its low half or in
/// both, the signed minimum of `i128`, and `2^128 - 1`, which overflows
/// `f32`.
#[test]
fn the_cases_reach_every_path_of_the_lowering() {
    let mut bits = Bits(0x2401);
    let c64 = cases(64, &mut bits);
    assert!(c64.iter().any(|&v| v >> 63 == 1 && v & 1 == 1));
    let c128 = cases(128, &mut bits);
    assert!(c128.contains(&(1 << 127)) && c128.contains(&u128::MAX));
    assert!(c128.iter().any(|&v| v >> 64 == 0 && v >> 63 == 1));
    assert_eq!(host(F32, 128, u128::MAX, false), 0x7f80_0000);
    assert_eq!(host(F32, 128, 1 << 127, true), 0xff00_0000);
    assert_eq!(host(F64, 1, 1, true), (-1.0f64).to_bits());
}
