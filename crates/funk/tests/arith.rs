//! `add`, `sub` and `mul` with each set of their flags, and `freeze`, run
//! natively at every width the backend lowers, on every pair of boundary
//! values (#14). Where a flag is broken the result is poison, which any
//! value refines (ADR-2026-10-29-2008), so there a test asks only for a
//! value of the type; everywhere else it asks for the exact result, wrapped.
//! A frozen value is one value: every use of it sees the same bits.

mod common;

use std::path::Path;

use common::{boundaries, build, expect, func, module, run, spell, text, wrap};
use funk_ir::dialects::core::WRAP_FLAG_SETS;
use funk_x86_64::width::SUPPORTED as WIDTHS;

/// The exact result of `op` on `a` and `b`, or `None` if it does not fit an
/// `i128`.
fn exact(op: &str, a: i128, b: i128) -> Option<i128> {
    match op {
        "add" => a.checked_add(b),
        "sub" => a.checked_sub(b),
        "mul" => a.checked_mul(b),
        _ => panic!("no op {op}"),
    }
}

/// Whether `op` with `flags` breaks a flag on `a` and `b`, two values of
/// `iW` read as signed, so that its result is poison.
fn breaks(w: u32, op: &str, flags: &[&str], a: i128, b: i128) -> bool {
    let m = 1i128 << w;
    let fits = |x: Option<i128>, lo: i128| x.is_some_and(|x| lo <= x && x < lo + m);
    let nuw = !fits(exact(op, a.rem_euclid(m), b.rem_euclid(m)), 0);
    let nsw = !fits(exact(op, a, b), -m / 2);
    (flags.contains(&"nuw") && nuw) || (flags.contains(&"nsw") && nsw)
}

/// Runs `exe` with `args` and checks that it prints one value of `iW`,
/// whichever it is: the result where the source's is poison.
fn expect_any(exe: &Path, args: &[&str], w: u32) {
    let out = run(exe, args);
    let stdout = text(&out.stdout);
    let value = stdout
        .strip_prefix("{\"values\":[\"")
        .and_then(|s| s.strip_suffix("\"]}\n"));
    let of_type = value.is_some_and(|v| match w {
        1 => v == "true" || v == "false",
        _ => v.parse::<i128>().is_ok_and(|x| wrap(w, x) == x),
    });
    assert!(
        out.status.code() == Some(0) && out.stderr.is_empty() && of_type,
        "{} {args:?}: {stdout}{}",
        exe.display(),
        text(&out.stderr)
    );
}

/// `op` and its flags, joined by `sep`: `add nuw nsw` or `add_nuw_nsw`.
fn joined(op: &str, flags: &[&str], sep: &str) -> String {
    let words: Vec<&str> = std::iter::once(op).chain(flags.iter().copied()).collect();
    words.join(sep)
}

/// Builds `@OP(%a: iW, %b: iW) -> iW` with each set of flags at each width,
/// and runs each function on every pair of boundary values.
fn runs_at_every_width(op: &str) {
    let mut poison = 0;
    for w in WIDTHS {
        let t = format!("i{w}");
        let funcs: Vec<String> = WRAP_FLAG_SETS
            .iter()
            .map(|fs| {
                let line = format!("%r: {t} = {} %a, %b", joined(op, fs, " "));
                let params = format!("%a: {t}, %b: {t}");
                func(&joined(op, fs, "_"), &params, &t, &[&line, "ret %r"])
            })
            .collect();
        let exe = build(&format!("arith-{op}-{w}"), &module(&funcs));
        for a in boundaries(w) {
            for b in boundaries(w) {
                let (sa, sb) = (spell(w, a), spell(w, b));
                for fs in WRAP_FLAG_SETS {
                    let args = [&format!("@{}", joined(op, fs, "_")), &sa, &sb];
                    let args = args.map(String::as_str);
                    if breaks(w, op, fs, a, b) {
                        poison += 1;
                        expect_any(&exe, &args, w);
                    } else {
                        let r = exact(op, a, b).expect("signed values of 64 bits at most");
                        expect(&exe, &args, &[&spell(w, wrap(w, r))]);
                    }
                }
            }
        }
    }
    assert!(poison > 0, "no boundary values break a flag of {op}");
}

#[test]
fn add_with_each_set_of_flags_runs_at_every_width() {
    runs_at_every_width("add");
}

#[test]
fn sub_with_each_set_of_flags_runs_at_every_width() {
    runs_at_every_width("sub");
}

#[test]
fn mul_with_each_set_of_flags_runs_at_every_width() {
    runs_at_every_width("mul");
}

#[test]
fn the_flags_break_where_lean_says_they_do() {
    // `#guard`s of `lean/Fir/Core/Wrap.lean` (#64), as signed values.
    for (w, op, flags, a, b, poison) in [
        (8, "add", "nuw", -56, 55, false),
        (8, "add", "nuw", -56, 56, true),
        (8, "add", "nsw", -56, 56, false),
        (8, "add", "nsw", 127, 1, true),
        (8, "add", "nsw", -128, -1, true),
        (8, "sub", "nuw", 1, 2, true),
        (8, "sub", "nsw", 1, 2, false),
        (8, "sub", "nsw", -128, 1, true),
        (8, "sub", "nuw", -1, -128, false),
        (8, "mul", "nuw", 16, 16, true),
        (8, "mul", "nsw", 16, 8, true),
        (8, "mul", "nsw", -16, 8, false),
        (8, "mul", "nuw", -16, 8, true),
        (1, "add", "nsw", -1, -1, true),
        (1, "add", "nuw", -1, -1, true),
        (1, "add", "nsw", -1, 0, false),
        (1, "sub", "nsw", 0, -1, true),
        (1, "sub", "nsw", -1, 0, false),
        (1, "sub", "nuw", 0, -1, true),
        (1, "mul", "nsw", -1, -1, true),
        (1, "mul", "nuw", -1, -1, false),
        (64, "sub", "nsw", 0, i128::from(i64::MIN), true),
        (64, "mul", "nsw", i128::from(i64::MIN), -1, true),
        (64, "mul", "nsw", i128::from(i64::MAX), -1, false),
    ] {
        assert_eq!(
            breaks(w, op, &[flags], a, b),
            poison,
            "{op} {flags} {a} {b} at i{w}"
        );
    }
}

#[test]
fn freeze_keeps_a_value_and_gives_poison_one_value_for_every_use() {
    for w in WIDTHS {
        let t = format!("i{w}");
        let params = format!("%a: {t}, %b: {t}");
        let op = |s: &str| s.replace("T", &t);
        let one = format!("%one: {t} = const {}", spell(w, 1));
        let funcs = [
            func("keep", &params, &t, &[&op("%f: T = freeze %a"), "ret %f"]),
            // `%p` is poison where `a + b` wraps, read as unsigned.
            func(
                "same",
                &params,
                &t,
                &[
                    &op("%p: T = add nuw %a, %b"),
                    &op("%f: T = freeze %p"),
                    &op("%d: T = sub %f, %f"),
                    "ret %d",
                ],
            ),
            // `%p` is poison where `a * b` overflows, read as signed;
            // `f + f` and `f * 2` agree only if both see the same `f`.
            func(
                "twice",
                &params,
                &t,
                &[
                    &op("%p: T = mul nsw %a, %b"),
                    &op("%f: T = freeze %p"),
                    &op("%s: T = add %f, %f"),
                    &one,
                    &op("%two: T = add %one, %one"),
                    &op("%m: T = mul %f, %two"),
                    &op("%d: T = sub %s, %m"),
                    "ret %d",
                ],
            ),
            func(
                "frozen",
                &params,
                &t,
                &[
                    &op("%p: T = add nsw %a, %b"),
                    &op("%f: T = freeze %p"),
                    "ret %f",
                ],
            ),
        ];
        let exe = build(&format!("freeze-{w}"), &module(&funcs));
        let zero = spell(w, 0);
        for a in boundaries(w) {
            for b in boundaries(w) {
                let (sa, sb) = (spell(w, a), spell(w, b));
                expect(&exe, &["@keep", &sa, &sb], &[&sa]);
                expect(&exe, &["@same", &sa, &sb], &[&zero]);
                expect(&exe, &["@twice", &sa, &sb], &[&zero]);
                if breaks(w, "add", &["nsw"], a, b) {
                    expect_any(&exe, &["@frozen", &sa, &sb], w);
                } else {
                    expect(&exe, &["@frozen", &sa, &sb], &[&spell(w, wrap(w, a + b))]);
                }
            }
        }
    }
}
