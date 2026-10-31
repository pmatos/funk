//! `icmp` with each of its ten predicates, run natively at every width the
//! backend lowers (#16), on every pair of boundary values, among them pairs
//! that are in one order read as signed and in the other read as unsigned.
//! A value of `iN` is the low `N` bits of its slot, and the bits above are
//! unspecified (ADR-2026-10-30-1231), so each predicate also runs on
//! operands that a wrapping `add` or a `shl` computed, whose slots hold
//! other bits above `N` than an argument's. A poison operand gives a poison
//! `i1`, which any value refines (ADR-2026-10-29-2008).

mod common;

use std::cmp::Ordering;
use std::path::Path;

use common::{boundaries, build, expect, expect_any, func, module, spell, wrap};
use funk_ir::dialects::core::PREDICATES;
use funk_x86_64::width::SUPPORTED as WIDTHS;

/// Whether `p` holds of `a` and `b`, two values of `iW` read as signed
/// (`Pred.holds` in `lean/Fir/Core/Compare.lean`, #77). `W` is at most 64.
fn holds(w: u32, p: &str, a: i128, b: i128) -> bool {
    let m = 1i128 << w;
    let (s, u) = (a.cmp(&b), a.rem_euclid(m).cmp(&b.rem_euclid(m)));
    match p {
        "eq" => a == b,
        "ne" => a != b,
        "slt" => s.is_lt(),
        "sle" => s.is_le(),
        "sgt" => s.is_gt(),
        "sge" => s.is_ge(),
        "ult" => u.is_lt(),
        "ule" => u.is_le(),
        "ugt" => u.is_gt(),
        "uge" => u.is_ge(),
        _ => panic!("no predicate {p}"),
    }
}

/// The `i1` that says `b`: `true` is -1 read as signed.
fn i1(b: bool) -> String {
    spell(1, -i128::from(b))
}

/// Runs `@name` of `exe` on `args`, values of `iW`, and checks that it
/// gives whether `p` holds of `a` and `b`.
fn check(exe: &Path, w: u32, name: &str, args: &[i128], (p, a, b): (&str, i128, i128)) {
    let args: Vec<String> = args.iter().map(|&v| spell(w, v)).collect();
    let mut all = vec![format!("@{name}")];
    all.extend(args);
    let all: Vec<&str> = all.iter().map(String::as_str).collect();
    expect(exe, &all, &[&i1(holds(w, p, a, b))]);
}

#[test]
fn every_predicate_runs_at_every_width_on_the_boundary_values() {
    let mut apart = 0;
    for w in WIDTHS {
        let t = format!("i{w}");
        let funcs: Vec<String> = PREDICATES
            .iter()
            .map(|p| {
                let line = format!("%r: i1 = icmp {p} %a, %b");
                func(p, &format!("%a: {t}, %b: {t}"), "i1", &[&line, "ret %r"])
            })
            .collect();
        let exe = build(&format!("icmp-{w}"), &module(&funcs));
        for a in boundaries(w) {
            for b in boundaries(w) {
                apart += usize::from(holds(w, "slt", a, b) != holds(w, "ult", a, b));
                for p in PREDICATES {
                    check(&exe, w, p, &[a, b], (p, a, b));
                }
            }
        }
    }
    // At each width, pairs such as (-1, 0) are in one order read as signed
    // and in the other read as unsigned.
    assert!(apart >= 2 * WIDTHS.len(), "{apart}");
}

/// The operands of a test at `iW`, each as two arguments and what the op
/// that combines them gives. `add` of the first pairs wraps: at `i8` to
/// `i32`, where arguments arrive sign-extended, its slot holds zeros above
/// a set top bit or ones above a clear one; at `i1`, where `true` is 1,
/// `true + true` is 2. `shl` by `N - 1` or by 1 moves a bit into the top
/// bit, or out of it, with no change above `N`.
fn computed(w: u32, op: &str) -> Vec<(i128, i128, i128)> {
    let [zero, one, minus, min, max] = boundaries(w)[..] else {
        return match op {
            "add" => vec![(-1, -1, 0), (-1, 0, -1), (0, 0, 0)],
            _ => vec![(-1, 0, -1), (0, 0, 0)],
        };
    };
    let pairs = match op {
        "add" => vec![
            (max, one),
            (min, minus),
            (minus, minus),
            (max, max),
            (min, min),
            (one, one),
            (zero, zero),
        ],
        _ => vec![
            (one, i128::from(w) - 1),
            (max, one),
            (min, one),
            (minus, one),
            (one, zero),
        ],
    };
    let gives = |(x, y): (i128, i128)| match op {
        "add" => wrap(w, x + y),
        _ => wrap(w, x << y),
    };
    pairs.into_iter().map(|p| (p.0, p.1, gives(p))).collect()
}

/// Builds, at each width, `@P(%x, %y, %u, %v) -> i1` for each predicate
/// `P`, which compares `op %x, %y` with `op %u, %v`, and runs it on every
/// pair of [`computed`] operands.
fn computed_operands_run_at_every_width(op: &str) {
    for w in WIDTHS {
        let t = format!("i{w}");
        let funcs: Vec<String> = PREDICATES
            .iter()
            .map(|p| {
                let params = format!("%x: {t}, %y: {t}, %u: {t}, %v: {t}");
                let ops = [
                    format!("%a: {t} = {op} %x, %y"),
                    format!("%b: {t} = {op} %u, %v"),
                    format!("%r: i1 = icmp {p} %a, %b"),
                    "ret %r".into(),
                ];
                let ops: Vec<&str> = ops.iter().map(String::as_str).collect();
                func(p, &params, "i1", &ops)
            })
            .collect();
        let exe = build(&format!("icmp-{op}-{w}"), &module(&funcs));
        for &(x, y, a) in &computed(w, op) {
            for &(u, v, b) in &computed(w, op) {
                for p in PREDICATES {
                    check(&exe, w, p, &[x, y, u, v], (p, a, b));
                }
            }
        }
    }
}

#[test]
fn operands_that_a_wrapping_add_computed_compare_by_their_low_bits() {
    computed_operands_run_at_every_width("add");
}

#[test]
fn operands_that_a_shl_computed_compare_by_their_low_bits() {
    computed_operands_run_at_every_width("shl");
}

#[test]
fn a_poison_operand_gives_any_i1() {
    // `%p` shifts by `N`, so it is poison (at `i1`, by `true`, which is 1).
    for w in WIDTHS {
        let t = format!("i{w}");
        let n = spell(w, if w == 1 { -1 } else { i128::from(w) });
        let funcs: Vec<String> = PREDICATES
            .iter()
            .flat_map(|p| {
                let head = [
                    format!("%n: {t} = const {n}"),
                    format!("%p: {t} = shl %a, %n"),
                ];
                [("l", "%p, %a"), ("r", "%a, %p"), ("b", "%p, %p")].map(|(side, args)| {
                    let mut ops = head.to_vec();
                    ops.push(format!("%r: i1 = icmp {p} {args}"));
                    ops.push("ret %r".into());
                    let ops: Vec<&str> = ops.iter().map(String::as_str).collect();
                    func(&format!("{p}_{side}"), &format!("%a: {t}"), "i1", &ops)
                })
            })
            .collect();
        let exe = build(&format!("icmp-poison-{w}"), &module(&funcs));
        for p in PREDICATES {
            for side in ["l", "r", "b"] {
                for a in boundaries(w) {
                    expect_any(&exe, &[&format!("@{p}_{side}"), &spell(w, a)], 1);
                }
            }
        }
    }
}

/// What the ten predicates give, in the order of [`PREDICATES`], on two
/// values in the order `s` read as signed and `u` read as unsigned
/// (`predResults` in `lean/Fir/Core/Compare.lean`, #77).
fn pred_results(s: Ordering, u: Ordering) -> [bool; 10] {
    use Ordering::{Equal, Greater, Less};
    [
        s == Equal,
        s != Equal,
        s == Less,
        s != Greater,
        s == Greater,
        s != Less,
        u == Less,
        u != Greater,
        u == Greater,
        u != Less,
    ]
}

#[test]
fn the_model_agrees_with_lean() {
    // The `#guard`s of `lean/Fir/Core/Compare.lean` (#77), as signed values:
    // `boundaryPairs` at `i7`, `i8`, `i33` and `i64`, and the pairs at `i1`.
    use Ordering::{Equal as E, Greater as G, Less as L};
    let check = |w: u32, a: i128, b: i128, s, u| {
        let got = PREDICATES.map(|p| holds(w, p, a, b));
        assert_eq!(got, pred_results(s, u), "{a} {b} at i{w}");
    };
    for w in [7, 8, 33, 64] {
        let (min, max) = (-(1i128 << (w - 1)), (1i128 << (w - 1)) - 1);
        for (a, b, s, u) in [
            (0, 0, E, E),
            (0, 1, L, L),
            (1, 0, G, G),
            (-1, 0, L, G),
            (0, -1, G, L),
            (-1, 1, L, G),
            (-1, -1, E, E),
            (min, max, L, G),
            (max, min, G, L),
            (min, 0, L, G),
            (max, -1, G, L),
            (min, -1, L, L),
            (1, max, L, L),
            (min, min, E, E),
        ] {
            check(w, a, b, s, u);
        }
    }
    // At `i1`, `true` is -1 read as signed and 1 read as unsigned.
    check(1, -1, 0, L, G);
    check(1, 0, -1, G, L);
    check(1, -1, -1, E, E);
    check(1, 0, 0, E, E);
    // At `i8`, -1 is less than 1 read as signed and greater read as
    // unsigned.
    assert!(holds(8, "slt", -1, 1) && !holds(8, "ult", -1, 1) && holds(8, "ugt", -1, 1));
    assert!(holds(8, "eq", 5, 5));
}
