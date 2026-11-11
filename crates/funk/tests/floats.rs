//! `f32` and `f64` run natively (#229): float constants, `fcmp` with each
//! of its fourteen predicates, and floats passed to and returned from
//! functions in SSE registers (ADR-2026-11-11-1140). A float constant is a
//! float literal, and a built executable reads and writes a float as its
//! bits read as a signed integer (ADR-2026-11-11-1438). Each comparison
//! is checked against the host's own IEEE 754 comparison, on zeros of both
//! signs, subnormals, ones, the largest finite values, infinities and NaNs,
//! quiet and signalling, with payloads and either sign.

mod common;

use std::path::Path;

use common::{build, expect, func, module};
use funk_ir::dialects::core::FLOAT_PREDICATES;

/// The hard bit patterns of `f32`.
const F32: [u32; 14] = [
    0x0000_0000, // +0
    0x8000_0000, // -0
    0x0000_0001, // the smallest subnormal
    0x8000_0001,
    0x007f_ffff, // the largest subnormal
    0x3f80_0000, // 1.0
    0xbf80_0000, // -1.0
    0x7f7f_ffff, // the largest finite value
    0x7f80_0000, // +inf
    0xff80_0000, // -inf
    0x7fc0_0000, // the quiet NaN
    0xffc0_0001, // a quiet NaN with its sign set and a payload
    0x7f80_0001, // a signalling NaN
    0xffff_ffff,
];

/// The hard bit patterns of `f64`.
const F64: [u64; 12] = [
    0,
    0x8000_0000_0000_0000,
    1,
    0x000f_ffff_ffff_ffff,
    0x3ff0_0000_0000_0000,
    0xbff0_0000_0000_0000,
    0x7fef_ffff_ffff_ffff,
    0x7ff0_0000_0000_0000,
    0xfff0_0000_0000_0000,
    0x7ff8_0000_0000_0000,
    0xfff0_0000_0000_0001,
    0x7ff4_0000_0000_0000,
];

/// Whether the float predicate `p` holds of two values that compare as `c`,
/// `None` when they are unordered (`FPred.holds` in
/// `lean/Fir/Core/FloatCompare.lean`).
fn holds(p: &str, c: Option<std::cmp::Ordering>) -> bool {
    use std::cmp::Ordering::*;
    match (p, c) {
        ("ord", c) => c.is_some(),
        ("uno", c) => c.is_none(),
        (p, None) => p.starts_with('u'),
        (p, Some(o)) => match &p[1..] {
            "eq" => o == Equal,
            "ne" => o != Equal,
            "lt" => o == Less,
            "le" => o != Greater,
            "gt" => o == Greater,
            "ge" => o != Less,
            _ => panic!("no predicate {p}"),
        },
    }
}

/// The module of `@cmp(%a: T, %b: T)`, which gives each predicate's
/// `fcmp` of `%a` and `%b`, in the order of [`FLOAT_PREDICATES`].
fn fcmps(t: &str) -> String {
    let mut body: Vec<String> = FLOAT_PREDICATES
        .iter()
        .map(|p| format!("%{p}: i1 = fcmp {p} %a, %b"))
        .collect();
    let names: Vec<String> = FLOAT_PREDICATES.iter().map(|p| format!("%{p}")).collect();
    body.push(format!("ret {}", names.join(", ")));
    let body: Vec<&str> = body.iter().map(String::as_str).collect();
    let results = vec!["i1"; FLOAT_PREDICATES.len()].join(", ");
    module(&[func("cmp", &format!("%a: {t}, %b: {t}"), &results, &body)])
}

/// Runs `@cmp` on `a` and `b`, which compare as `c`, and checks each
/// predicate's result.
fn check(exe: &Path, a: &str, b: &str, c: Option<std::cmp::Ordering>) {
    let want: Vec<&str> = FLOAT_PREDICATES
        .iter()
        .map(|p| if holds(p, c) { "true" } else { "false" })
        .collect();
    expect(exe, &["@cmp", a, b], &want);
}

#[test]
fn every_predicate_runs_at_f32_on_the_hard_values() {
    let exe = build("fcmp-f32", &fcmps("f32"));
    for &a in &F32 {
        for &b in &F32 {
            let c = f32::from_bits(a).partial_cmp(&f32::from_bits(b));
            check(&exe, &(a as i32).to_string(), &(b as i32).to_string(), c);
        }
    }
}

#[test]
fn every_predicate_runs_at_f64_on_the_hard_values() {
    let exe = build("fcmp-f64", &fcmps("f64"));
    for &a in &F64 {
        for &b in &F64 {
            let c = f64::from_bits(a).partial_cmp(&f64::from_bits(b));
            check(&exe, &(a as i64).to_string(), &(b as i64).to_string(), c);
        }
    }
}

/// Floats pass in `%xmm0` to `%xmm7` apart from the integers, then on the
/// stack, and come back in `%xmm0` and `%xmm1`, or in the result area: each
/// argument comes back as its bits, at every position.
#[test]
fn floats_pass_and_return_in_sse_registers_and_on_the_stack() {
    let params: Vec<String> = (0..18)
        .map(|k| format!("%x{k}: {}", ["f64", "i64", "f32"][k % 3]))
        .collect();
    let params = params.join(", ");
    let callee = func("g", &params, "f32, f64, i64", &["ret %x17, %x15, %x16"]);
    let args: Vec<String> = (0..18).map(|k| format!("%x{k}")).collect();
    let call = format!("%a: f32, %b: f64, %c: i64 = call @g {}", args.join(", "));
    let caller = func("f", &params, "f64, f32", &[&call, "ret %b, %a"]);
    let two = func("two", "%x: f32, %y: f64", "f64, f32", &["ret %y, %x"]);
    let exe = build("float-abi", &module(&[callee, caller, two]));
    let bits = |k: usize| match k % 3 {
        0 => (0x4000_0000_0000_0000i64 + k as i64).to_string(),
        1 => (-(k as i64)).to_string(),
        _ => (0x3f80_0000 + k as i32).to_string(),
    };
    let args: Vec<String> = (0..18).map(bits).collect();
    let mut all = vec!["@f".to_string()];
    all.extend(args.iter().cloned());
    let all: Vec<&str> = all.iter().map(String::as_str).collect();
    expect(&exe, &all, &[&args[15], &args[17]]);
    expect(&exe, &["@two", "-4194304", "-1"], &["-1", "-4194304"]);
}

/// A constant gives its bits, each NaN's payload and sign included, and a
/// comparison of a NaN constant with itself is unordered.
#[test]
fn float_constants_give_their_bits() {
    let k = func(
        "k",
        "",
        "f32, f64, f32, i1, i1",
        &[
            "%a: f32 = const 0xffc00001",
            "%b: f64 = const 0x7ff8000000000001",
            "%c: f32 = const -0.0",
            "%e: i1 = fcmp oeq %a, %a",
            "%u: i1 = fcmp uno %c, %c",
            "ret %a, %b, %c, %e, %u",
        ],
    );
    let exe = build("float-const", &module(&[k]));
    expect(
        &exe,
        &["@k"],
        &[
            "-4194303",
            "9221120237041090561",
            "-2147483648",
            "false",
            "false",
        ],
    );
}
