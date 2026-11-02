//! `select`, run natively at every width the backend lowers (#16): with
//! each condition on every pair of boundary values, with a condition that
//! an `icmp` computed, and with a condition whose slot holds bits above bit
//! 0, which `select` must not read (ADR-2026-10-30-1231,
//! ADR-2026-10-31-0215). A poison condition, or a poison value that
//! `select` chooses, gives poison, which any value refines
//! (ADR-2026-10-29-2008); a poison value that it does not choose does not
//! matter.

mod common;

use std::path::Path;

use common::{boundaries, build, expect, expect_any, func, module, spell, wrap};
use funk_ir::dialects::core::PREDICATES;
use funk_x86_64::width::SUPPORTED as WIDTHS;

/// `select` on `c`, `a` and `b`, each `None` where it is poison
/// (`selectValues` in `lean/Fir/Core/Compare.lean`, #77).
fn select(c: Option<bool>, a: Option<i128>, b: Option<i128>) -> Option<i128> {
    if c? { a } else { b }
}

/// Runs `@name` of `exe` on `args` and checks that it gives `r`, a value
/// of `iW`, or any value of the type where `r` is poison.
fn check(exe: &Path, w: u32, name: &str, args: &[String], r: Option<i128>) {
    let mut all = vec![format!("@{name}")];
    all.extend(args.iter().cloned());
    let all: Vec<&str> = all.iter().map(String::as_str).collect();
    match r {
        Some(v) => expect(exe, &all, &[&spell(w, v)]),
        None => expect_any(exe, &all, w),
    }
}

/// The `i1` that says `b`: `true` is -1 read as signed.
fn i1(b: bool) -> String {
    spell(1, -i128::from(b))
}

/// The text of `@name(params) -> iW` with the ops `ops`, then `ret %r`.
fn function(name: &str, params: &str, w: u32, ops: &[String]) -> String {
    let mut ops: Vec<&str> = ops.iter().map(String::as_str).collect();
    ops.push("ret %r");
    func(name, params, &format!("i{w}"), &ops)
}

#[test]
fn select_chooses_by_its_condition_at_every_width() {
    for w in WIDTHS {
        let t = format!("i{w}");
        let line = format!("%r: {t} = select %c, %a, %b");
        let f = function("sel", &format!("%c: i1, %a: {t}, %b: {t}"), w, &[line]);
        let exe = build(&format!("select-{w}"), &module(&[f]));
        for c in [false, true] {
            for a in boundaries(w) {
                for b in boundaries(w) {
                    let args = [i1(c), spell(w, a), spell(w, b)];
                    check(&exe, w, "sel", &args, select(Some(c), Some(a), Some(b)));
                }
            }
        }
    }
}

#[test]
fn a_condition_that_icmp_computed_chooses() {
    // `select (icmp p %a, %b), %a, %b`, as a minimum or a maximum is
    // written, with each predicate.
    for w in WIDTHS {
        let t = format!("i{w}");
        let funcs: Vec<String> = PREDICATES
            .iter()
            .map(|p| {
                let ops = [
                    format!("%c: i1 = icmp {p} %a, %b"),
                    format!("%r: {t} = select %c, %a, %b"),
                ];
                function(p, &format!("%a: {t}, %b: {t}"), w, &ops)
            })
            .collect();
        let exe = build(&format!("select-icmp-{w}"), &module(&funcs));
        let m = 1i128 << w;
        for a in boundaries(w) {
            for b in boundaries(w) {
                let (s, u) = (a.cmp(&b), a.rem_euclid(m).cmp(&b.rem_euclid(m)));
                for (p, c) in PREDICATES.into_iter().zip([
                    s.is_eq(),
                    s.is_ne(),
                    s.is_lt(),
                    s.is_le(),
                    s.is_gt(),
                    s.is_ge(),
                    u.is_lt(),
                    u.is_le(),
                    u.is_gt(),
                    u.is_ge(),
                ]) {
                    let args = [spell(w, a), spell(w, b)];
                    check(&exe, w, p, &args, select(Some(c), Some(a), Some(b)));
                }
            }
        }
    }
}

#[test]
fn select_reads_only_bit_0_of_its_condition() {
    // `@sum` adds two `i1`: `true + true` leaves 2 in the slot, which is
    // `false` with bit 1 set. `@low` truncates an `iK` to its bit 0, a
    // copy, so the bits above stay: 2, -2 and the signed minimum are
    // `false` with bits set above bit 0, and 3, -1 and the signed maximum
    // are `true`.
    for w in WIDTHS {
        let t = format!("i{w}");
        let line = format!("%r: {t} = select %c, %a, %b");
        let sum = function(
            "sum",
            &format!("%x: i1, %y: i1, %a: {t}, %b: {t}"),
            w,
            &["%c: i1 = add %x, %y".into(), line.clone()],
        );
        let mut funcs = vec![sum];
        for k in [8, 16, 32, 64] {
            let ops = ["%c: i1 = trunc %k".to_string(), line.clone()];
            let params = format!("%k: i{k}, %a: {t}, %b: {t}");
            funcs.push(function(&format!("low{k}"), &params, w, &ops));
        }
        let exe = build(&format!("select-bit0-{w}"), &module(&funcs));
        for a in boundaries(w) {
            for b in boundaries(w).into_iter().filter(|&b| b != a) {
                let arms = [spell(w, a), spell(w, b)];
                for (x, y) in [(true, true), (true, false), (false, true), (false, false)] {
                    let args = [i1(x), i1(y), arms[0].clone(), arms[1].clone()];
                    check(&exe, w, "sum", &args, select(Some(x ^ y), Some(a), Some(b)));
                }
                for k in [8u32, 16, 32, 64] {
                    let (min, max) = (-(1i128 << (k - 1)), (1i128 << (k - 1)) - 1);
                    for v in [2, -2, min, 0, 3, -1, max, 1] {
                        let args = [spell(k, v), arms[0].clone(), arms[1].clone()];
                        let r = select(Some(v & 1 == 1), Some(a), Some(b));
                        check(&exe, w, &format!("low{k}"), &args, r);
                    }
                }
            }
        }
    }
}

#[test]
fn values_that_a_wrapping_add_computed_are_chosen_by_their_low_bits() {
    // `%a` and `%b` are sums that wrap, so their slots hold other bits
    // above `N` than an argument's; the result is the chosen sum's value.
    for w in WIDTHS {
        let t = format!("i{w}");
        let ops = [
            format!("%a: {t} = add %x, %y"),
            format!("%b: {t} = add %u, %v"),
            format!("%r: {t} = select %c, %a, %b"),
        ];
        let params = format!("%c: i1, %x: {t}, %y: {t}, %u: {t}, %v: {t}");
        let exe = build(
            &format!("select-sum-{w}"),
            &module(&[function("f", &params, w, &ops)]),
        );
        let min = -(1i128 << (w - 1));
        let max = -min - 1;
        let sums = [(max, max), (min, min), (max, -1), (min, -1), (-1, -1)];
        for c in [false, true] {
            for &(x, y) in &sums {
                for &(u, v) in &sums {
                    let args = [i1(c), spell(w, x), spell(w, y), spell(w, u), spell(w, v)];
                    let (a, b) = (wrap(w, x + y), wrap(w, u + v));
                    check(&exe, w, "f", &args, select(Some(c), Some(a), Some(b)));
                }
            }
        }
    }
}

#[test]
fn poison_matters_only_in_the_condition_and_the_chosen_value() {
    // `%p` and `%q` shift by `N`, so they are poison (at `i1`, by `true`,
    // which is 1), and so is `%k`, which compares `%p`. `@first` and
    // `@second` choose between a value and poison, `@cond` and `@cmp` choose
    // on a poison condition, and `@both` chooses poison either way.
    for w in WIDTHS {
        let t = format!("i{w}");
        let n = spell(w, if w == 1 { -1 } else { i128::from(w) });
        let head = |r: &str| {
            vec![
                format!("%n: {t} = const {n}"),
                format!("%p: {t} = shl %a, %n"),
                "%one: i1 = const true".to_string(),
                "%q: i1 = shl %c, %one".to_string(),
                "%k: i1 = icmp eq %p, %p".to_string(),
                format!("%r: {t} = {r}"),
            ]
        };
        let params = format!("%c: i1, %a: {t}, %b: {t}");
        let funcs: Vec<String> = [
            ("first", "select %c, %b, %p"),
            ("second", "select %c, %p, %b"),
            ("cond", "select %q, %a, %b"),
            ("cmp", "select %k, %a, %b"),
            ("both", "select %c, %p, %p"),
        ]
        .map(|(name, r)| function(name, &params, w, &head(r)))
        .to_vec();
        let exe = build(&format!("select-poison-{w}"), &module(&funcs));
        for c in [false, true] {
            for a in boundaries(w) {
                for b in boundaries(w) {
                    let args = [i1(c), spell(w, a), spell(w, b)];
                    for (name, r) in [
                        ("first", select(Some(c), Some(b), None)),
                        ("second", select(Some(c), None, Some(b))),
                        ("cond", select(None, Some(a), Some(b))),
                        ("cmp", select(None, Some(a), Some(b))),
                        ("both", select(Some(c), None, None)),
                    ] {
                        check(&exe, w, name, &args, r);
                    }
                }
            }
        }
    }
}

#[test]
fn the_model_agrees_with_lean() {
    // The `#guard`s of `selectValues` in `lean/Fir/Core/Compare.lean` (#77),
    // as signed values.
    let (min7, max7) = (-64, 63);
    let (min64, max64) = (i128::from(i64::MIN), i128::from(i64::MAX));
    let max33 = (1i128 << 32) - 1;
    for (c, a, b, r) in [
        (Some(true), Some(0), Some(-1), Some(0)),
        (Some(false), Some(0), Some(-1), Some(-1)),
        (Some(true), Some(min7), Some(max7), Some(min7)),
        (Some(false), Some(min7), Some(max7), Some(max7)),
        (Some(true), Some(-1), Some(1), Some(-1)),
        (Some(false), Some(-1), Some(1), Some(1)),
        (Some(true), Some(max33), Some(0), Some(max33)),
        (Some(false), Some(max64), Some(min64), Some(min64)),
        (Some(true), Some(i128::MIN), Some(-1), Some(i128::MIN)),
        (None, Some(7), Some(7), None),
        (None, None, None, None),
        (Some(true), Some(7), None, Some(7)),
        (Some(false), None, Some(min64), Some(min64)),
        (Some(true), Some(-1), None, Some(-1)),
        (Some(true), None, Some(7), None),
        (Some(false), Some(7), None, None),
        (Some(true), None, None, None),
    ] {
        assert_eq!(select(c, a, b), r, "{c:?} {a:?} {b:?}");
    }
}
