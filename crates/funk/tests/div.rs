//! `sdiv` and `udiv` with and without `exact`, `srem` and `urem`, run
//! natively at every width the backend lowers (#18), on dividends and
//! divisors of both signs and the boundary values. A run whose result is
//! UB in the spec, a zero divisor or the signed minimum divided by `-1`, is
//! skipped: native code may do anything there (ADR-2026-10-31-0050). Where
//! `exact` is broken the result is poison, which any value refines
//! (ADR-2026-10-29-2008), so there a test asks only for a value of the type.

mod common;

use std::path::Path;

use common::{boundaries, build, expect, func, module, run, spell, text, wrap};
use funk_ir::dialects::core::DIVISION_OPS;
use funk_x86_64::width::SUPPORTED as WIDTHS;

/// How an op ends on two values (`divEv` in `lean/Fir/Core/Div.lean`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Ends {
    /// With this value, read as signed.
    Value(i128),
    /// With poison: `exact` is broken.
    Poison,
    /// With immediate UB.
    Ub,
}

/// How `op`, with `exact` if set, ends on `a` and `b`, two values of `iW`
/// read as signed. `W` is at most 64.
fn divide(w: u32, op: &str, exact: bool, a: i128, b: i128) -> Ends {
    let m = 1i128 << w;
    let signed = op.starts_with('s');
    if b == 0 || (signed && a == -m / 2 && b == -1) {
        return Ends::Ub;
    }
    let (x, y) = if signed {
        (a, b)
    } else {
        (a.rem_euclid(m), b.rem_euclid(m))
    };
    // Rust's `/` rounds towards zero, and `%` takes the dividend's sign.
    let (q, r) = (x / y, x % y);
    match op {
        "sdiv" | "udiv" if exact && r != 0 => Ends::Poison,
        "sdiv" | "udiv" => Ends::Value(wrap(w, q)),
        _ => Ends::Value(wrap(w, r)),
    }
}

/// Each op with each set of its flags, as the text writes it and as a
/// function's name: (`sdiv exact`, `sdiv_exact`, `sdiv`, true).
fn spellings() -> Vec<(String, String, &'static str, bool)> {
    let mut out = Vec::new();
    for (op, has_exact) in DIVISION_OPS {
        out.push((op.to_string(), op.to_string(), op, false));
        if has_exact {
            out.push((format!("{op} exact"), format!("{op}_exact"), op, true));
        }
    }
    out
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

/// Runs `@name` of `exe` on `args` and checks what it gives against
/// `ends`. Returns whether the result is poison.
fn check(exe: &Path, w: u32, name: &str, args: &[String], ends: Ends) -> bool {
    let mut all = vec![format!("@{name}")];
    all.extend(args.iter().cloned());
    let all: Vec<&str> = all.iter().map(String::as_str).collect();
    match ends {
        Ends::Value(v) => expect(exe, &all, &[&spell(w, v)]),
        Ends::Poison => expect_any(exe, &all, w),
        Ends::Ub => panic!("{name} {args:?} is UB at i{w}: it must not run"),
    }
    ends == Ends::Poison
}

/// The values that each test divides at `iW`: the boundary values, and at
/// `i8` and wider, small values of both signs that leave remainders.
fn values(w: u32) -> Vec<i128> {
    let mut vs = boundaries(w);
    if w >= 8 {
        vs.extend([2, -2, 3, -3, 7, -7]);
    }
    vs
}

/// Builds `@OP(%a: iW, %b: iW) -> iW` for each op and set of flags, as
/// the executable `exe_name`, and runs each on every pair of `vs` whose
/// result is not UB. Returns how many runs it skipped and how many gave
/// poison.
fn runs_on_every_pair(exe_name: &str, w: u32, vs: &[i128]) -> (usize, usize) {
    let t = format!("i{w}");
    let funcs: Vec<String> = spellings()
        .iter()
        .map(|(op, name, ..)| {
            let line = format!("%r: {t} = {op} %a, %b");
            func(name, &format!("%a: {t}, %b: {t}"), &t, &[&line, "ret %r"])
        })
        .collect();
    let exe = build(exe_name, &module(&funcs));
    let (mut skipped, mut poison) = (0, 0);
    for &a in vs {
        for &b in vs {
            let args = [spell(w, a), spell(w, b)];
            for (_, name, op, exact) in spellings() {
                match divide(w, op, exact, a, b) {
                    Ends::Ub => skipped += 1,
                    ends => poison += usize::from(check(&exe, w, &name, &args, ends)),
                }
            }
        }
    }
    (skipped, poison)
}

#[test]
fn each_op_and_flag_runs_at_every_width() {
    for w in WIDTHS {
        let (skipped, poison) = runs_on_every_pair(&format!("div-{w}"), w, &values(w));
        assert!(skipped > 0, "no UB skipped at i{w}");
        assert_eq!(poison > 0, w > 1, "exact broken at i{w}: {poison}");
    }
}

#[test]
fn i8_divides_through_ax() {
    // `idivb` and `divb` divide `%ax` and leave the quotient in `%al` and
    // the remainder in `%ah`: quotients and remainders of every sign, and
    // those whose top bit is set.
    let vs = [-128, -127, -100, -7, -2, -1, 0, 1, 2, 7, 100, 126, 127];
    runs_on_every_pair("div-ax", 8, &vs);
}

#[test]
fn the_bits_above_the_width_do_not_change_the_result() {
    // The dividend is a sum and the divisor a difference of parameters,
    // which may leave a carry or a borrow above `N` bits: the op reads only
    // the low `N` bits. At `i1`, `true + true` is `false` with bit 1 set,
    // and `false - true` is `true` with every bit set.
    for w in WIDTHS {
        let t = format!("i{w}");
        let funcs: Vec<String> = spellings()
            .iter()
            .map(|(op, name, ..)| {
                let ops = [
                    &format!("%x: {t} = add %a, %b"),
                    &format!("%y: {t} = sub %c, %d"),
                    &format!("%r: {t} = {op} %x, %y"),
                    "ret %r",
                ];
                let params = format!("%a: {t}, %b: {t}, %c: {t}, %d: {t}");
                func(name, &params, &t, &ops)
            })
            .collect();
        let exe = build(&format!("div-carry-{w}"), &module(&funcs));
        let (sums, differences) = match boundaries(w)[..] {
            [zero, one, minus, min, max] => (
                vec![
                    (max, one),
                    (min, minus),
                    (minus, minus),
                    (max, max),
                    (min, min),
                    (one, one),
                ],
                vec![
                    (min, one),
                    (max, minus),
                    (min, max),
                    (zero, min),
                    (one, max),
                    (minus, one),
                ],
            ),
            _ => (vec![(0, -1), (-1, -1), (-1, 0)], vec![(0, -1), (-1, 0)]),
        };
        for &(a, b) in &sums {
            for &(c, d) in &differences {
                let (x, y) = (wrap(w, a + b), wrap(w, c - d));
                let args = [a, b, c, d].map(|v| spell(w, v));
                for (_, name, op, exact) in spellings() {
                    let ends = divide(w, op, exact, x, y);
                    if ends != Ends::Ub {
                        check(&exe, w, &name, &args, ends);
                    }
                }
            }
        }
    }
}

#[test]
fn the_model_agrees_with_lean() {
    // `#guard`s of `lean/Fir/Core/Div.lean` (#68), as signed values.
    use Ends::{Poison, Ub, Value};
    let (min64, max64) = (i128::from(i64::MIN), i128::from(i64::MAX));
    let (min33, max33) = (-(1i128 << 32), (1i128 << 32) - 1);
    for (w, op, exact, a, b, ends) in [
        (8, "sdiv", false, -7, 2, Value(-3)),
        (8, "sdiv", false, 7, -2, Value(-3)),
        (8, "sdiv", false, 127, -1, Value(-127)),
        (8, "sdiv", false, -128, -128, Value(1)),
        (8, "sdiv", false, -128, -1, Ub),
        (8, "sdiv", false, 5, 0, Ub),
        (8, "sdiv", true, -6, 3, Value(-2)),
        (8, "sdiv", true, -7, -2, Poison),
        (8, "sdiv", true, -128, 2, Value(-64)),
        (8, "sdiv", true, -128, -1, Ub),
        (8, "udiv", false, -1, 2, Value(127)),
        (8, "udiv", false, -128, -1, Value(0)),
        (8, "udiv", false, 127, -128, Value(0)),
        (8, "udiv", true, -2, 2, Value(127)),
        (8, "udiv", true, -2, -1, Poison),
        (8, "udiv", true, -1, -1, Value(1)),
        (8, "srem", false, -7, 2, Value(-1)),
        (8, "srem", false, 7, -2, Value(1)),
        (8, "srem", false, -128, 3, Value(-2)),
        (8, "srem", false, 127, -1, Value(0)),
        (8, "srem", false, -128, -1, Ub),
        (8, "urem", false, -1, 2, Value(1)),
        (8, "urem", false, -128, -1, Value(-128)),
        (8, "urem", false, 127, -128, Value(127)),
        (8, "urem", false, 5, 0, Ub),
        // At `i1`, `true` is -1, the signed minimum and all ones.
        (1, "sdiv", false, -1, -1, Ub),
        (1, "sdiv", true, -1, -1, Ub),
        (1, "sdiv", false, 0, -1, Value(0)),
        (1, "sdiv", true, 0, -1, Value(0)),
        (1, "sdiv", false, -1, 0, Ub),
        (1, "srem", false, -1, -1, Ub),
        (1, "srem", false, 0, -1, Value(0)),
        (1, "udiv", false, -1, -1, Value(-1)),
        (1, "udiv", true, 0, -1, Value(0)),
        (1, "udiv", false, -1, 0, Ub),
        (1, "urem", false, -1, -1, Value(0)),
        (7, "sdiv", false, -64, -1, Ub),
        (7, "sdiv", true, 63, 2, Poison),
        (7, "udiv", true, -2, 63, Value(2)),
        (7, "srem", false, -64, 63, Value(-1)),
        (7, "urem", false, -64, 63, Value(1)),
        (33, "sdiv", false, max33, -1, Value(min33 + 1)),
        (33, "udiv", false, min33, 2, Value(1 << 31)),
        (33, "srem", false, min33, max33, Value(-1)),
        (33, "urem", false, -1, min33, Value(max33)),
        (64, "sdiv", false, min64, -1, Ub),
        (64, "sdiv", false, -1, min64, Value(0)),
        (64, "sdiv", true, min64, max64, Poison),
        (64, "udiv", false, -1, min64, Value(1)),
        (64, "udiv", true, min64, min64, Value(1)),
        (64, "srem", false, min64, max64, Value(-1)),
        (64, "urem", false, min64, max64, Value(1)),
    ] {
        assert_eq!(
            divide(w, op, exact, a, b),
            ends,
            "{op} exact={exact} {a} {b} at i{w}"
        );
    }
}
