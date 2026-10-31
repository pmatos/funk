//! Loops built from `br` and `cond_br` (#19), run natively at every width
//! the backend lowers: the spec's `@sum` (`lean/Fir/Text/Example.lean`), an
//! iterative factorial and Euclid's gcd. Each loop passes its state round
//! as block arguments, so each trip is a parallel move
//! (ADR-2026-10-31-0335), and each test of a loop is a `cond_br` on an
//! `icmp` (ADR-2026-10-30-1231).
//!
//! A loop runs once per unit of its input, so the inputs here are the
//! boundary values of each width that end within 2^15 trips, and small
//! values whose results wrap.

mod common;

use std::path::Path;

use common::{boundaries, build, expect, expect_any, module, spell, wrap};
use funk_x86_64::width::SUPPORTED as WIDTHS;

/// The most trips a test asks a loop to make.
const TRIPS: i128 = 1 << 15;

/// The spec's `@sum` at `iW`: the integers from 0 up to `%n`, with `nsw`.
fn sum_text(w: u32) -> String {
    let (zero, one) = (spell(w, 0), spell(w, 1));
    format!(
        "func @sum_{w}(%n: i{w}) -> i{w} {{
^entry:
  %zero: i{w} = const {zero} @0
  br ^loop(%zero, %zero) @0
^loop(%i: i{w}, %acc: i{w}):
  %done: i1 = icmp sge %i, %n @0
  cond_br %done, ^exit(%acc), ^body @0
^body:
  %acc1: i{w} = add nsw %acc, %i @0
  %one: i{w} = const {one} @0
  %i1: i{w} = add nsw %i, %one @0
  br ^loop(%i1, %acc1) @0
^exit(%r: i{w}):
  ret %r @0
}}
"
    )
}

/// `@sum` at `iW` on `n`: `None` where an `add nsw` overflows, which gives
/// poison. `%i` counts up to `n`, which is at most the maximum, so only
/// `%acc` can overflow.
fn sum(w: u32, n: i128) -> Option<i128> {
    let total = (0..n.max(0)).sum::<i128>();
    (wrap(w, total) == total).then_some(total)
}

/// An iterative factorial at `iW`, with no flags: `%acc` takes the product
/// of `%i` while `%i` is above zero, read as signed.
fn fact_text(w: u32) -> String {
    let (zero, one) = (spell(w, 0), spell(w, 1));
    format!(
        "func @fact_{w}(%n: i{w}) -> i{w} {{
^entry:
  %one: i{w} = const {one} @0
  %zero: i{w} = const {zero} @0
  br ^loop(%n, %one) @0
^loop(%i: i{w}, %acc: i{w}):
  %more: i1 = icmp sgt %i, %zero @0
  cond_br %more, ^body, ^exit(%acc) @0
^body:
  %acc1: i{w} = mul %acc, %i @0
  %i1: i{w} = sub %i, %one @0
  br ^loop(%i1, %acc1) @0
^exit(%r: i{w}):
  ret %r @0
}}
"
    )
}

/// The factorial of `n` at `iW`, wrapped: 1 when `n` is not above zero.
fn fact(w: u32, n: i128) -> i128 {
    wrap(w, (1..=n.max(0)).fold(1, |acc, i| wrap(w, acc * i)))
}

/// Euclid's gcd at `iW`, on the values read as unsigned. Each trip passes
/// `%x mod %y` and `%y` to `^loop(%y, %x)`: the move into `%x` must read
/// `%y` before the move into `%y`, which the branch writes first, writes
/// it.
fn gcd_text(w: u32) -> String {
    let zero = spell(w, 0);
    format!(
        "func @gcd_{w}(%a: i{w}, %b: i{w}) -> i{w} {{
^entry:
  %zero: i{w} = const {zero} @0
  br ^loop(%b, %a) @0
^loop(%y: i{w}, %x: i{w}):
  %done: i1 = icmp eq %y, %zero @0
  cond_br %done, ^exit(%x), ^body @0
^body:
  %r: i{w} = urem %x, %y @0
  br ^loop(%r, %y) @0
^exit(%g: i{w}):
  ret %g @0
}}
"
    )
}

/// The gcd of `a` and `b` read as unsigned at `iW`, read back as signed.
fn gcd(w: u32, a: i128, b: i128) -> i128 {
    let m = 1i128 << w;
    let (mut x, mut y) = (a.rem_euclid(m), b.rem_euclid(m));
    while y != 0 {
        (x, y) = (y, x % y);
    }
    wrap(w, x)
}

#[test]
fn the_models_give_what_lean_gives() {
    // `lean/FirTest/Loops.lean` (#81): `@sum` gives 45 at 10, and its loop
    // at i8 overflows `add nsw` past 15; 5! is 120; gcd(1071, 462) is 21.
    assert_eq!(sum(32, 10), Some(45));
    assert_eq!(sum(8, 16), Some(120));
    assert_eq!(sum(8, 17), None);
    assert_eq!(sum(1, -1), Some(0));
    assert_eq!(fact(64, 5), 120);
    assert_eq!(fact(64, 20), 2_432_902_008_176_640_000);
    assert_eq!(fact(8, 5), 120);
    assert_eq!(fact(8, 6), wrap(8, 720));
    assert_eq!(fact(1, -1), -1);
    assert_eq!(gcd(64, 1071, 462), 21);
    assert_eq!(gcd(8, -1, 5), 5);
    assert_eq!(gcd(8, -128, 96), 32);
    assert_eq!(gcd(16, 0, 0), 0);
}

/// Inputs of `iW` for a loop that runs once per unit: the boundary values
/// that end within [`TRIPS`] trips, and small ones whose results wrap.
fn inputs(w: u32) -> Vec<i128> {
    let mut out: Vec<i128> = boundaries(w).into_iter().filter(|&n| n <= TRIPS).collect();
    for n in [2, 3, 5, 10, 12, 13, 15, 16, 17, 20, 21, 25, 100, 255, 256] {
        let n = wrap(w, n);
        if !out.contains(&n) {
            out.push(n);
        }
    }
    out
}

fn run(exe: &Path, w: u32, name: &str, args: &[i128], want: Option<i128>) {
    let mut all = vec![format!("@{name}_{w}")];
    all.extend(args.iter().map(|&v| spell(w, v)));
    let all: Vec<&str> = all.iter().map(String::as_str).collect();
    match want {
        Some(v) => expect(exe, &all, &[&spell(w, v)]),
        None => expect_any(exe, &all, w),
    }
}

#[test]
fn the_spec_s_sum_runs_and_gives_45_at_10() {
    // The text of `lean/Fir/Text/Example.lean`, without `@sum10`, whose
    // `call` is #20's.
    let text = "func @sum(%n: i32) -> i32 {
^entry:
  %zero: i32 = const 0 @1
  br ^loop(%zero, %zero) @1
^loop(%i: i32, %acc: i32):
  %done: i1 = icmp sge %i, %n @2
  cond_br %done, ^exit(%acc), ^body @2
^body:
  %acc1: i32 = add nsw %acc, %i @3
  %one: i32 = const 1 @3
  %i1: i32 = add nsw %i, %one @3
  br ^loop(%i1, %acc1) @3
^exit(%r: i32):
  ret %r @4
}

locs {
  @0 = unknown
  @1 = \"sum.c\":2:3 to 2:15
  @2 = \"sum.c\":3:10 to 3:16
  @3 = \"sum.c\":4:5 to 4:17
  @4 = \"sum.c\":6:3 to 6:14
}
";
    let exe = build("loops-spec-sum", text);
    for (n, want) in [
        ("10", "45"),
        ("0", "0"),
        ("1", "0"),
        ("2", "1"),
        ("-7", "0"),
    ] {
        expect(&exe, &["@sum", n], &[want]);
    }
    expect(&exe, &["@sum", "1000"], &["499500"]);
}

#[test]
fn sum_factorial_and_gcd_run_at_every_width() {
    for w in WIDTHS {
        let exe = build(
            &format!("loops-{w}"),
            &module(&[sum_text(w), fact_text(w), gcd_text(w)]),
        );
        for n in inputs(w) {
            run(&exe, w, "sum", &[n], sum(w, n));
            run(&exe, w, "fact", &[n], Some(fact(w, n)));
        }
        let mut pairs = boundaries(w);
        pairs.extend([12, 18, 35, 64, 96, 462, 1071].map(|v| wrap(w, v)));
        for &a in &pairs {
            for &b in &pairs {
                run(&exe, w, "gcd", &[a, b], Some(gcd(w, a, b)));
            }
        }
    }
}
