//! The float arithmetic runs natively at `f32` and `f64` (#229,
//! `docs/decisions/x86-64-backend-lowering.md#float-arithmetic`): `fadd`,
//! `fsub`, `fmul`, `fdiv`, `sqrt`, `fneg`, `fabs` and `fma`. Each result is
//! checked against the host's own IEEE 754 arithmetic, on the hard values
//! (zeros of both signs, subnormals, ones, the largest finite values,
//! infinities and NaNs) and, for `fma`, whose lowering calls a routine of
//! its own, on many random operands as well: products that cancel against
//! the addend, results far below the smallest normal number, and results
//! that overflow. A NaN result may be any NaN (ADR-2026-11-09-1549), so
//! where the host gives a NaN the test asks only for a NaN.
//!
//! Each batch is one function that applies its op to constants and returns
//! every result, so one build and one run check many cases.

mod common;

use common::{build, func, module, run, text};
use funk_ir::dialects::core::spell_float;

/// A float format the backend lowers, with the host's arithmetic on it.
#[derive(Clone, Copy)]
struct Format {
    name: &'static str,
    e: u32,
    m: u32,
}

const F32: Format = Format {
    name: "f32",
    e: 8,
    m: 23,
};

const F64: Format = Format {
    name: "f64",
    e: 11,
    m: 52,
};

impl Format {
    fn width(self) -> u32 {
        1 + self.e + self.m
    }

    /// The bits of a value of the format: its low `width` bits.
    fn mask(self) -> u64 {
        u64::MAX >> (64 - self.width())
    }

    fn is_nan(self, b: u64) -> bool {
        let exp = (b >> self.m) & ((1 << self.e) - 1);
        exp == (1 << self.e) - 1 && b & ((1 << self.m) - 1) != 0
    }

    /// The host's result of `op` on the bits `x`.
    fn host(self, op: &str, x: &[u64]) -> u64 {
        if self.width() == 32 {
            let f: Vec<f32> = x.iter().map(|&b| f32::from_bits(b as u32)).collect();
            let r = match op {
                "fadd" => f[0] + f[1],
                "fsub" => f[0] - f[1],
                "fmul" => f[0] * f[1],
                "fdiv" => f[0] / f[1],
                "sqrt" => f[0].sqrt(),
                "fneg" => -f[0],
                "fabs" => f[0].abs(),
                _ => f[0].mul_add(f[1], f[2]),
            };
            u64::from(r.to_bits())
        } else {
            let f: Vec<f64> = x.iter().map(|&b| f64::from_bits(b)).collect();
            let r = match op {
                "fadd" => f[0] + f[1],
                "fsub" => f[0] - f[1],
                "fmul" => f[0] * f[1],
                "fdiv" => f[0] / f[1],
                "sqrt" => f[0].sqrt(),
                "fneg" => -f[0],
                "fabs" => f[0].abs(),
                _ => f[0].mul_add(f[1], f[2]),
            };
            r.to_bits()
        }
    }
}

/// The hard bit patterns of `f`.
fn hard(f: Format) -> Vec<u64> {
    if f.width() == 32 {
        vec![
            0,
            0x8000_0000,
            1,
            0x8000_0001,
            0x007f_ffff,
            0x0080_0000,
            0x3f80_0000,
            0xbf80_0000,
            0x3f80_0001,
            0x4040_0000,
            0x7f7f_ffff,
            0x7f80_0000,
            0xff80_0000,
            0x7fc0_0000,
            0xffc0_0001,
            0x7f80_0001,
        ]
    } else {
        vec![
            0,
            0x8000_0000_0000_0000,
            1,
            0x8000_0000_0000_0001,
            0x000f_ffff_ffff_ffff,
            0x0010_0000_0000_0000,
            0x3ff0_0000_0000_0000,
            0xbff0_0000_0000_0000,
            0x3ff0_0000_0000_0001,
            0x4008_0000_0000_0000,
            0x7fef_ffff_ffff_ffff,
            0x7ff0_0000_0000_0000,
            0xfff0_0000_0000_0000,
            0x7ff8_0000_0000_0000,
            0xfff0_0000_0000_0001,
            0x7ff4_0000_0000_0000,
        ]
    }
}

/// The text of op `op`, with its attribute when it rounds.
fn op_text(op: &str) -> String {
    match op {
        "fneg" | "fabs" => op.to_string(),
        _ => format!("{op} round(rne)"),
    }
}

/// Runs `op` on each case of `cases` at `f` natively, and returns the bits
/// of each result.
fn native(name: &str, f: Format, op: &str, cases: &[Vec<u64>]) -> Vec<u64> {
    let t = f.name;
    let mut body = Vec::new();
    let mut results = Vec::new();
    for (i, case) in cases.iter().enumerate() {
        let mut operands = Vec::new();
        for (j, &b) in case.iter().enumerate() {
            let lit = spell_float(f.e, f.m, u128::from(b));
            body.push(format!("%c{i}_{j}: {t} = const {lit}"));
            operands.push(format!("%c{i}_{j}"));
        }
        body.push(format!(
            "%r{i}: {t} = {} {}",
            op_text(op),
            operands.join(", ")
        ));
        results.push(format!("%r{i}"));
    }
    body.push(format!("ret {}", results.join(", ")));
    let body: Vec<&str> = body.iter().map(String::as_str).collect();
    let types = vec![t; cases.len()].join(", ");
    let exe = build(name, &module(&[func("batch", "", &types, &body)]));
    let out = run(&exe, &["@batch"]);
    let stdout = text(&out.stdout);
    assert_eq!(out.status.code(), Some(0), "{stdout}{}", text(&out.stderr));
    let values = stdout
        .trim_end()
        .strip_prefix("{\"values\":[")
        .and_then(|s| s.strip_suffix("]}"))
        .expect("a JSON line of values");
    values
        .split(',')
        .map(|v| v.trim_matches('"').parse::<i64>().expect("a float's bits") as u64 & f.mask())
        .collect()
}

/// Checks `op` on every case at `f`, in batches of 64, against the host.
fn check(name: &str, f: Format, op: &str, cases: &[Vec<u64>]) {
    for (n, batch) in cases.chunks(64).enumerate() {
        let got = native(&format!("{name}-{n}"), f, op, batch);
        for (case, &g) in batch.iter().zip(&got) {
            let want = f.host(op, case);
            let ok = if f.is_nan(want) {
                f.is_nan(g)
            } else {
                g == want
            };
            assert!(ok, "{op} at {} of {case:x?}: {g:#x}, not {want:#x}", f.name);
        }
    }
}

/// Every case of `n` operands drawn from the hard values of `f`.
fn hard_cases(f: Format, n: usize) -> Vec<Vec<u64>> {
    let values = hard(f);
    let mut cases = vec![vec![]];
    for _ in 0..n {
        cases = cases
            .into_iter()
            .flat_map(|c| {
                values.iter().map(move |&v| {
                    let mut c = c.clone();
                    c.push(v);
                    c
                })
            })
            .collect();
    }
    cases
}

#[test]
fn each_op_of_two_operands_runs_on_the_hard_values() {
    for f in [F32, F64] {
        for op in ["fadd", "fsub", "fmul", "fdiv"] {
            check(&format!("{op}-{}", f.name), f, op, &hard_cases(f, 2));
        }
    }
}

#[test]
fn each_op_of_one_operand_runs_on_the_hard_values() {
    for f in [F32, F64] {
        for op in ["sqrt", "fneg", "fabs"] {
            check(&format!("{op}-{}", f.name), f, op, &hard_cases(f, 1));
        }
    }
}

/// `fneg` and `fabs` change only the sign bit, a NaN's too.
#[test]
fn fneg_and_fabs_keep_a_nan_s_payload() {
    for f in [F32, F64] {
        let sign = 1u64 << (f.width() - 1);
        let nans: Vec<Vec<u64>> = hard(f)
            .into_iter()
            .filter(|&b| f.is_nan(b))
            .map(|b| vec![b])
            .collect();
        let neg = native(&format!("fneg-nan-{}", f.name), f, "fneg", &nans);
        let abs = native(&format!("fabs-nan-{}", f.name), f, "fabs", &nans);
        for ((x, n), a) in nans.iter().zip(neg).zip(abs) {
            assert_eq!((n, a), (x[0] ^ sign, x[0] & !sign), "{x:x?}");
        }
    }
}

#[test]
fn fma_runs_on_the_hard_values() {
    for f in [F32, F64] {
        check(&format!("fma-{}", f.name), f, "fma", &hard_cases(f, 3));
    }
}

/// A xorshift generator, so that each run draws the same operands.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    /// A float of `f` whose exponent field lies in `lo..hi`.
    fn float(&mut self, f: Format, lo: u64, hi: u64) -> u64 {
        let mantissa = self.next() & ((1 << f.m) - 1);
        let exponent = lo + self.next() % (hi - lo);
        let sign = self.next() & 1;
        (sign << (f.width() - 1)) | (exponent << f.m) | mantissa
    }
}

/// Random operands of `fma` at `f`: any bits; a product and the negation
/// of its rounded value, nudged, so that they cancel; products and addends
/// near and below the smallest normal number; and near the largest.
fn random_fma(f: Format, rng: &mut Rng) -> Vec<Vec<u64>> {
    let top = (1u64 << f.e) - 1;
    let bias = top / 2;
    let mut cases = Vec::new();
    for _ in 0..128 {
        cases.push((0..3).map(|_| rng.next() & f.mask()).collect());
    }
    for _ in 0..256 {
        let a = rng.float(f, bias - 20, bias + 20);
        let b = rng.float(f, bias - 20, bias + 20);
        let p = f.host("fmul", &[a, b]) ^ (1 << (f.width() - 1));
        let nudge = rng.next() % 3;
        let c = match nudge {
            0 => p,
            1 => p + 1,
            _ => p - 1,
        };
        cases.push(vec![a, b, c]);
    }
    for _ in 0..256 {
        let a = rng.float(f, 0, bias / 2);
        let b = rng.float(f, bias / 2, bias + 4);
        let c = rng.float(f, 0, 3);
        cases.push(vec![a, b, c]);
    }
    for _ in 0..128 {
        let a = rng.float(f, top - bias / 2, top);
        let b = rng.float(f, bias, bias + bias / 2);
        let c = rng.float(f, top - 4, top);
        cases.push(vec![a, b, c]);
    }
    cases
}

/// Operands of `fma` at `f32` whose exact result lies above a tie of `f32`
/// by less than an ulp of `f64`: `a * b` is half an ulp of `c` and a tail
/// that `f64` cannot hold. Rounding the sum to `f64` first, to nearest or
/// toward zero, lands on the tie, which then goes to the even neighbour,
/// below the exact result. With `a = (1 + i * 2^-23) * 2^-24` and
/// `b = 1 - (2i - 1) * 2^-24`, `a * b` is `2^-24` and a little more.
fn f32_double_rounding() -> Vec<Vec<u64>> {
    let mut cases = Vec::new();
    for i in 1984u64..2049 {
        let a = 0x3380_0000 | i;
        let b = u64::from((((1u64 << 24) - (2 * i - 1)) as f32 / (1u64 << 24) as f32).to_bits());
        for c in [0x3f80_0000u64, 0x3f80_0002] {
            cases.push(vec![a, b, c]);
            cases.push(vec![a | 0x8000_0000, b, c | 0x8000_0000]);
        }
    }
    cases
}

#[test]
fn fma_at_f32_rounds_once_where_a_double_rounding_would_tie() {
    let cases = f32_double_rounding();
    let rounds_twice = |case: &Vec<u64>| {
        let x: Vec<f64> = case
            .iter()
            .map(|&b| f64::from(f32::from_bits(b as u32)))
            .collect();
        u64::from(((x[0] * x[1] + x[2]) as f32).to_bits())
    };
    assert!(cases.iter().any(|c| rounds_twice(c) != F32.host("fma", c)));
    check("fma-double-rounding", F32, "fma", &cases);
}

#[test]
fn fma_rounds_once_on_random_operands() {
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    for f in [F32, F64] {
        let cases = random_fma(f, &mut rng);
        check(&format!("fma-random-{}", f.name), f, "fma", &cases);
    }
}
