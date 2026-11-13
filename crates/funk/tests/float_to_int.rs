//! `fptosi` and `fptoui` run natively from `f32` and `f64` to `i1`, `i8`,
//! `i16`, `i32`, `i64` and `i128` (#241,
//! `docs/decisions/x86-64-backend-lowering-floats.md#conversions-to-integers`).
//! Each truncates toward zero (the human's ruling of 2026-11-12 on #354).
//!
//! Where the source gives an integer, the native result must be it: the
//! host's `trunc` of the float, which is exact, read as an integer. Where
//! the source gives poison, an integer that `iN` does not hold, an infinity
//! or a NaN, any value of `iN` refines it (ADR-2026-10-30-2248), so the run
//! must only print one. Rust's `as` saturates there and sends a NaN to `0`,
//! which is one such value, so it is not compared.
//!
//! The cases are the zeros, the smallest subnormal, the values just below
//! and above `1`, fractions such as `2.7`, each power of two that bounds a
//! width with the floats next to it, the largest finite value, the
//! infinities and NaNs, each of either sign, and random values whose
//! exponents span every width. Each operand is a `bitcast` of an integer
//! constant, so any bit pattern is a case, and each batch is one function
//! that returns every result, so one build and one run check many cases.

mod common;

use common::{Bits, build, json_values, module, returning, run_func, spell, wrap};

/// The widths the backend lowers.
const WIDTHS: [u32; 6] = [1, 8, 16, 32, 64, 128];

/// A float format the backend lowers: its name, the integer type of its
/// bits, its width and the bits of its mantissa.
#[derive(Clone, Copy)]
struct Format {
    name: &'static str,
    bits_type: &'static str,
    bits: u32,
    mantissa: u32,
}

const F32: Format = Format {
    name: "f32",
    bits_type: "i32",
    bits: 32,
    mantissa: 23,
};

const F64: Format = Format {
    name: "f64",
    bits_type: "i64",
    bits: 64,
    mantissa: 52,
};

impl Format {
    /// The float with the bits `b`, as an `f64`, which holds it exactly.
    fn value(self, b: u64) -> f64 {
        if self.bits == 32 {
            f64::from(f32::from_bits(b as u32))
        } else {
            f64::from_bits(b)
        }
    }

    /// The bits of `x`, rounded into the format.
    fn bits_of(self, x: f64) -> u64 {
        if self.bits == 32 {
            u64::from((x as f32).to_bits())
        } else {
            x.to_bits()
        }
    }

    /// The bits of the format's integer type that hold the float `b`, as a
    /// constant of it.
    fn constant(self, b: u64) -> i64 {
        if self.bits == 32 {
            i64::from(b as u32 as i32)
        } else {
            b as i64
        }
    }
}

/// The cases of `f`, as bits.
fn cases(f: Format, bits: &mut Bits) -> Vec<u64> {
    let mut base = vec![
        0.0,
        0.5,
        0.999_999_9,
        1.0,
        1.5,
        2.7,
        3.0,
        255.9,
        f64::from(f32::MAX),
        f64::MAX,
        f64::INFINITY,
        f64::NAN,
    ];
    for k in [1, 7, 8, 15, 16, 31, 32, 52, 53, 63, 64, 100, 127, 128] {
        base.push(2f64.powi(k));
    }
    let sign = 1u64 << (f.bits - 1);
    // The smallest subnormal, and a quiet NaN with a payload.
    let nan = if f.bits == 32 {
        0x7fc0_0001
    } else {
        0x7ff8_0000_0000_0001
    };
    let mut out = vec![1, nan];
    for x in base {
        let b = f.bits_of(x);
        // The float itself and the two next to it, of the same sign.
        out.extend([b, b.wrapping_sub(1) & (sign - 1), b + 1]);
    }
    out.extend(out.clone().into_iter().map(|b| b | sign));
    // Random values: an exponent from -2 to 130, or to `f32`'s largest,
    // any mantissa and either sign.
    let bias = (1u64 << (f.bits - 2 - f.mantissa)) - 1;
    let span = if f.bits == 32 { 130 } else { 133 };
    for _ in 0..96 {
        let r = bits.next();
        let exp = bias - 2 + (r >> 32) % span;
        let mantissa = r & ((1 << f.mantissa) - 1);
        out.push((((r >> 31) & 1) * sign) | (exp << f.mantissa) | mantissa);
    }
    let mask = u64::MAX >> (64 - f.bits);
    let mut out: Vec<u64> = out.into_iter().map(|b| b & mask).collect();
    out.sort_unstable();
    out.dedup();
    out
}

/// The integer that the source gives for the float `x` at `iW`, signed
/// when `signed`, read as a signed value of `iW`: `x` truncated toward zero
/// when `iW` holds it, and none where the source gives poison.
fn source(x: f64, w: u32, signed: bool) -> Option<i128> {
    if !x.is_finite() {
        return None;
    }
    let t = x.trunc();
    let top = 2f64.powi(w as i32);
    if signed {
        (t >= -top / 2.0 && t < top / 2.0).then_some(t as i128)
    } else if t >= 0.0 && t < top {
        let u = t as u128;
        Some(if w == 128 {
            u as i128
        } else {
            wrap(w, u as i128)
        })
    } else {
        None
    }
}

/// Converts each case of `f` to each width with `op` natively, in batches
/// of 64, and checks each result where the source gives one.
fn check(f: Format, op: &str) {
    let signed = op == "fptosi";
    let cs = cases(f, &mut Bits(0x2414));
    let mut funcs = Vec::new();
    let mut batches = Vec::new();
    for w in WIDTHS {
        for (n, batch) in cs.chunks(64).enumerate() {
            let mut body = Vec::new();
            for (i, &b) in batch.iter().enumerate() {
                body.push(format!("%b{i}: {} = const {}", f.bits_type, f.constant(b)));
                body.push(format!("%c{i}: {} = bitcast %b{i}", f.name));
                body.push(format!("%r{i}: i{w} = {op} %c{i}"));
            }
            let name = format!("i{w}_{n}");
            funcs.push(returning(&name, body, &format!("i{w}"), batch.len()));
            batches.push((name, w, batch.to_vec()));
        }
    }
    let exe = build(&format!("{op}-{}", f.name), &module(&funcs));
    for (name, w, batch) in batches {
        let stdout = run_func(&exe, &name);
        let got = json_values(&stdout);
        assert_eq!(got.len(), batch.len(), "{stdout}");
        for (&b, &g) in batch.iter().zip(&got) {
            match source(f.value(b), w, signed) {
                Some(v) => assert_eq!(g, spell(w, v), "{op} of {} {b:#x} to i{w}", f.name),
                None if w == 1 => assert!(g == "true" || g == "false", "{g}"),
                None => assert!(g.parse::<i128>().is_ok(), "{op} of {b:#x} to i{w}: {g}"),
            }
        }
    }
}

#[test]
fn fptosi_from_f32_truncates_toward_zero() {
    check(F32, "fptosi");
}

#[test]
fn fptosi_from_f64_truncates_toward_zero() {
    check(F64, "fptosi");
}

#[test]
fn fptoui_from_f32_truncates_toward_zero() {
    check(F32, "fptoui");
}

#[test]
fn fptoui_from_f64_truncates_toward_zero() {
    check(F64, "fptoui");
}

/// The cases reach every path of the lowering and both sides of every
/// range: an unsigned `i64` of `2^63` or more, an `i128` shifted left past
/// its low half, `-2^127`, and the values just inside and just outside each
/// width.
#[test]
fn the_cases_reach_every_edge() {
    let c64 = cases(F64, &mut Bits(0x2414));
    let has = |x: f64| c64.contains(&x.to_bits());
    assert!(has(2f64.powi(63)) && has(-(2f64.powi(127))) && has(2f64.powi(100)));
    assert!(c64.contains(&(2f64.powi(64).to_bits() - 1)));
    assert!(has(-0.5) && has(2.7) && has(-2.7));
    assert_eq!(source(2.7, 32, true), Some(2));
    assert_eq!(source(-2.7, 32, true), Some(-2));
    assert_eq!(source(-0.5, 8, false), Some(0));
    assert_eq!(source(-1.0, 8, false), None);
    assert_eq!(source(2f64.powi(31), 32, true), None);
    assert_eq!(source(-(2f64.powi(31)), 32, true), Some(-(1 << 31)));
    assert_eq!(source(2f64.powi(31), 32, false), Some(-(1 << 31)));
    assert_eq!(source(-1.0, 1, true), Some(-1));
    assert_eq!(source(1.0, 1, true), None);
    assert_eq!(source(f64::NAN, 64, false), None);
    let below = f64::from_bits(2f64.powi(128).to_bits() - 1);
    assert_eq!(source(below, 128, false), Some(below as u128 as i128));
    assert_eq!(source(2f64.powi(128), 128, false), None);
    let c32 = cases(F32, &mut Bits(0x2414));
    assert!(c32.contains(&0x4f00_0000) && c32.contains(&0x4eff_ffff));
    assert!(c32.contains(&0xcf00_0000) && c32.contains(&0xcf00_0001));
}
