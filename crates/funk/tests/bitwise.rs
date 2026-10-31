//! The bitwise ops `and`, `or` and `xor`, and the shifts `shl`, `lshr` and
//! `ashr`, run natively at every width the backend lowers (#15). The
//! bitwise ops run on every pair of boundary values. The shifts run each
//! boundary value by the amounts 0, 1 and `N - 1`, which must give the
//! exact result, and by `N`, `N + 1` and the boundary values read as
//! unsigned, of which those of `N` or more give poison: any value of the
//! type refines it (ADR-2026-10-29-2008), so there a test asks only for a
//! value of the type. At `i1` the amounts are `false` (0) and `true` (1,
//! which is `N`). A shift whose operands are sums that wrap, so that the
//! bits above `N` in their registers are not an extension of their values,
//! gives the exact result too (ADR-2026-10-30-1231).

mod common;

use std::path::Path;

use common::{boundaries, build, expect, expect_any, func, module, spell, wrap};
use funk_x86_64::width::SUPPORTED as WIDTHS;

/// The result of `op` on `a` and `b`, two values of `iW` read as signed, or
/// `None` where it is poison: a shift by an amount, read as unsigned, of
/// `N` or more.
fn exact(w: u32, op: &str, a: i128, b: i128) -> Option<i128> {
    let m = 1i128 << w;
    let amount = b.rem_euclid(m);
    let r = match op {
        "and" => a & b,
        "or" => a | b,
        "xor" => a ^ b,
        _ if amount >= i128::from(w) => return None,
        "shl" => a << amount,
        "lshr" => a.rem_euclid(m) >> amount,
        "ashr" => a >> amount,
        _ => panic!("no op {op}"),
    };
    Some(wrap(w, r))
}

/// The shift amounts that are less than `N`: 0, 1 and `N - 1`, or at `i1`
/// only 0.
fn in_range(w: u32) -> Vec<i128> {
    let mut ks = vec![0, 1, i128::from(w) - 1];
    ks.retain(|&k| k < i128::from(w));
    ks.dedup();
    ks
}

/// The shift amounts of a test, read as signed: those of [`in_range`],
/// `N`, `N + 1` and the boundary values. At `i1`, `false` and `true`.
fn amounts(w: u32) -> Vec<i128> {
    if w == 1 {
        return boundaries(1);
    }
    let n = i128::from(w);
    let mut ks = in_range(w);
    for k in [n, n + 1].into_iter().chain(boundaries(w)) {
        if !ks.contains(&k) {
            ks.push(k);
        }
    }
    ks
}

/// Runs the function `f` of `exe` on `args`, values of `iW`, and checks
/// that it gives `op` of `a` and `b`: the exact result, or any value of the
/// type where that is poison.
fn check(exe: &Path, w: u32, op: &str, f: &str, args: &[i128], a: i128, b: i128) {
    let args: Vec<String> = args.iter().map(|&v| spell(w, v)).collect();
    let args: Vec<&str> = std::iter::once(f)
        .chain(args.iter().map(String::as_str))
        .collect();
    match exact(w, op, a, b) {
        Some(r) => expect(exe, &args, &[&spell(w, r)]),
        None => expect_any(exe, &args, w),
    }
}

/// Builds `@OP(%a: iW, %b: iW) -> iW` at each width, and runs it on every
/// pair of boundary values.
fn bitwise_runs_at_every_width(op: &str) {
    for w in WIDTHS {
        let t = format!("i{w}");
        let line = format!("%r: {t} = {op} %a, %b");
        let f = func(op, &format!("%a: {t}, %b: {t}"), &t, &[&line, "ret %r"]);
        let exe = build(&format!("bitwise-{op}-{w}"), &module(&[f]));
        for a in boundaries(w) {
            for b in boundaries(w) {
                check(&exe, w, op, &format!("@{op}"), &[a, b], a, b);
            }
        }
    }
}

/// Builds, at each width, `@OP(%a: iW, %n: iW) -> iW` and `@sum(%x, %y,
/// %u, %v)`, which shifts `x + y` by `u + v`. Runs `@OP` on each boundary
/// value by each of [`amounts`], and `@sum` on every pair of boundary
/// values by each of [`in_range`], made as `min + (min + k)`: a sum whose
/// bits above `N` are all ones.
fn shift_runs_at_every_width(op: &str) {
    let mut poison = 0;
    for w in WIDTHS {
        let t = format!("i{w}");
        let line = format!("%r: {t} = {op} %a, %n");
        let plain = func(op, &format!("%a: {t}, %n: {t}"), &t, &[&line, "ret %r"]);
        let sum = func(
            "sum",
            &format!("%x: {t}, %y: {t}, %u: {t}, %v: {t}"),
            &t,
            &[
                &format!("%a: {t} = add %x, %y"),
                &format!("%n: {t} = add %u, %v"),
                &line,
                "ret %r",
            ],
        );
        let exe = build(&format!("shift-{op}-{w}"), &module(&[plain, sum]));
        for a in boundaries(w) {
            for n in amounts(w) {
                poison += usize::from(exact(w, op, a, n).is_none());
                check(&exe, w, op, &format!("@{op}"), &[a, n], a, n);
            }
        }
        let min = -(1i128 << (w - 1));
        for x in boundaries(w) {
            for y in boundaries(w) {
                for k in in_range(w) {
                    let args = [x, y, min, wrap(w, min + k)];
                    check(&exe, w, op, "@sum", &args, wrap(w, x + y), k);
                }
            }
        }
    }
    assert!(poison > 0, "no amount of N or more for {op}");
}

#[test]
fn and_runs_at_every_width() {
    bitwise_runs_at_every_width("and");
}

#[test]
fn or_runs_at_every_width() {
    bitwise_runs_at_every_width("or");
}

#[test]
fn xor_runs_at_every_width() {
    bitwise_runs_at_every_width("xor");
}

#[test]
fn shl_runs_at_every_width() {
    shift_runs_at_every_width("shl");
}

#[test]
fn lshr_runs_at_every_width() {
    shift_runs_at_every_width("lshr");
}

#[test]
fn ashr_runs_at_every_width() {
    shift_runs_at_every_width("ashr");
}

#[test]
fn the_rules_agree_with_lean() {
    // `#guard`s of `lean/Fir/Core/Bitwise.lean` (#67), as signed values.
    let (min8, max8) = (-128, 127);
    let (min64, max64) = (i128::from(i64::MIN), i128::from(i64::MAX));
    for (w, op, a, b, r) in [
        (1, "and", -1, -1, Some(-1)),
        (1, "and", -1, 0, Some(0)),
        (1, "or", 0, -1, Some(-1)),
        (1, "xor", -1, -1, Some(0)),
        (1, "shl", -1, 0, Some(-1)),
        (1, "lshr", -1, -1, None),
        (1, "ashr", 0, -1, None),
        (8, "and", -1, min8, Some(min8)),
        (8, "or", min8, max8, Some(-1)),
        (8, "xor", max8, 1, Some(126)),
        (8, "shl", 1, 7, Some(min8)),
        (8, "shl", -1, 7, Some(min8)),
        (8, "shl", max8, 1, Some(-2)),
        (8, "lshr", min8, 7, Some(1)),
        (8, "lshr", -1, 1, Some(max8)),
        (8, "ashr", min8, 7, Some(-1)),
        (8, "ashr", min8, 1, Some(-64)),
        (8, "ashr", max8, 7, Some(0)),
        (8, "shl", 1, 8, None),
        (8, "lshr", -1, 9, None),
        (8, "ashr", 0, min8, None),
        (8, "shl", 1, -1, None),
        (64, "and", min64, -1, Some(min64)),
        (64, "xor", max64, -1, Some(min64)),
        (64, "shl", 1, 63, Some(min64)),
        (64, "shl", min64, 1, Some(0)),
        (64, "lshr", -1, 63, Some(1)),
        (64, "ashr", min64, 63, Some(-1)),
        (64, "ashr", max64, 62, Some(1)),
        (64, "shl", 1, 64, None),
        (64, "lshr", 1, min64, None),
        (64, "ashr", 1, -1, None),
    ] {
        assert_eq!(exact(w, op, a, b), r, "{op} {a} {b} at i{w}");
    }
}

#[test]
fn xor_of_a_frozen_shift_by_n_is_zero() {
    // `%p` is poison, `%f` one value of the type, and `f ^ f` is `0`.
    for w in WIDTHS {
        let t = format!("i{w}");
        let n = spell(w, if w == 1 { -1 } else { i128::from(w) });
        let f = func(
            "f",
            &format!("%a: {t}"),
            &t,
            &[
                &format!("%n: {t} = const {n}"),
                &format!("%p: {t} = shl %a, %n"),
                &format!("%f: {t} = freeze %p"),
                &format!("%r: {t} = xor %f, %f"),
                "ret %r",
            ],
        );
        let exe = build(&format!("frozen-shift-{w}"), &module(&[f]));
        for a in boundaries(w) {
            expect(&exe, &["@f", &spell(w, a)], &[&spell(w, 0)]);
        }
    }
}
