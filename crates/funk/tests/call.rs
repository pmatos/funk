//! Calls between funk functions (#20), run natively at every width the
//! backend lowers: direct recursion (factorial and Fibonacci), mutual
//! recursion (even and odd), a call with no result, and callees whose names
//! are not words. Recursion stays shallow: each input recurses at most 20
//! deep. `call_args.rs` has the calls with more than six arguments and the
//! spec's example module.

mod common;

use std::path::Path;

use common::{boundaries, build, expect, module, spell, wrap};
use funk_x86_64::width::ONE_REGISTER as WIDTHS;

/// A recursive factorial at `iW`, with no flags: `%n` times the factorial
/// of `%n - 1` while `%n` is above zero, read as signed, and 1 otherwise.
/// `%n` is used again after the call, so the caller's slots must survive
/// it.
fn fact_text(w: u32) -> String {
    let (zero, one) = (spell(w, 0), spell(w, 1));
    format!(
        "func @fact_{w}(%n: i{w}) -> i{w} {{
^entry:
  %zero: i{w} = const {zero} @0
  %more: i1 = icmp sgt %n, %zero @0
  cond_br %more, ^rec, ^base @0
^rec:
  %one: i{w} = const {one} @0
  %m: i{w} = sub %n, %one @0
  %f: i{w} = call @fact_{w} %m @0
  %p: i{w} = mul %n, %f @0
  ret %p @0
^base:
  %b: i{w} = const {one} @0
  ret %b @0
}}
"
    )
}

/// The factorial of `n` at `iW`, wrapped: 1 when `n` is not above zero.
fn fact(w: u32, n: i128) -> i128 {
    if n > 0 {
        wrap(w, n * fact(w, n - 1))
    } else {
        wrap(w, 1)
    }
}

/// A recursive Fibonacci at `iW`: `%n` when it is at most 1 read as
/// unsigned, and otherwise the sum of the two calls before it.
fn fib_text(w: u32) -> String {
    let one = spell(w, 1);
    format!(
        "func @fib_{w}(%n: i{w}) -> i{w} {{
^entry:
  %one: i{w} = const {one} @0
  %small: i1 = icmp ule %n, %one @0
  cond_br %small, ^base, ^rec @0
^base:
  ret %n @0
^rec:
  %a: i{w} = sub %n, %one @0
  %b: i{w} = sub %a, %one @0
  %fa: i{w} = call @fib_{w} %a @0
  %fb: i{w} = call @fib_{w} %b @0
  %s: i{w} = add %fa, %fb @0
  ret %s @0
}}
"
    )
}

/// The `n`-th Fibonacci number at `iW`, wrapped, for a small `n`.
fn fib(w: u32, n: i128) -> i128 {
    let (mut a, mut b) = (0, 1);
    for _ in 0..n {
        (a, b) = (b, a + b);
    }
    wrap(w, a)
}

/// `@even_W` and `@odd_W`, which call each other on `%n - 1` until `%n`
/// is zero.
fn parity_text(w: u32) -> String {
    let (zero, one) = (spell(w, 0), spell(w, 1));
    let half = |name: &str, other: &str, at_zero: &str| {
        format!(
            "func @{name}_{w}(%n: i{w}) -> i1 {{
^entry:
  %zero: i{w} = const {zero} @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^stop, ^more @0
^stop:
  %r: i1 = const {at_zero} @0
  ret %r @0
^more:
  %one: i{w} = const {one} @0
  %m: i{w} = sub %n, %one @0
  %o: i1 = call @{other}_{w} %m @0
  ret %o @0
}}
"
        )
    };
    half("even", "odd", "true") + "\n" + &half("odd", "even", "false")
}

/// Small inputs of `iW` that recurse at most 20 deep, from `from` up: the
/// boundary values among them and some between.
fn small(w: u32, from: i128) -> Vec<i128> {
    let mut out: Vec<i128> = boundaries(w).into_iter().filter(|&n| n <= 20).collect();
    for n in [2, 3, 5, 7, 10, 12, 13, 15, 16, 17, 20] {
        if wrap(w, n) == n && !out.contains(&n) {
            out.push(n);
        }
    }
    out.retain(|&n| n >= from);
    out
}

fn run(exe: &Path, name: &str, w: u32, n: i128, want: &str) {
    expect(exe, &[&format!("@{name}_{w}"), &spell(w, n)], &[want]);
}

#[test]
fn the_models_give_what_the_definitions_give() {
    assert_eq!(fact(64, 5), 120);
    assert_eq!(fact(64, 20), 2_432_902_008_176_640_000);
    assert_eq!(fact(8, 6), wrap(8, 720));
    assert_eq!(fact(32, -128), 1);
    assert_eq!(fact(1, 0), -1);
    assert_eq!(fib(64, 10), 55);
    assert_eq!(fib(8, 15), wrap(8, 610));
    assert_eq!(fib(1, 1), -1);
    assert_eq!(small(8, 0), [0, 1, 2, 3, 5, 7, 10, 12, 13, 15, 16, 17, 20]);
    assert_eq!(small(1, i128::MIN), [0, -1]);
}

#[test]
fn factorial_and_fibonacci_call_themselves_at_every_width() {
    for w in WIDTHS {
        let exe = build(
            &format!("call-rec-{w}"),
            &module(&[fact_text(w), fib_text(w)]),
        );
        // Every input at or below zero returns at once: the minimum too.
        for n in small(w, i128::MIN) {
            run(&exe, "fact", w, n, &spell(w, fact(w, n)));
        }
        for n in small(w, 0) {
            run(&exe, "fib", w, n, &spell(w, fib(w, n)));
        }
        if w == 1 {
            run(&exe, "fib", w, -1, "true");
        }
    }
}

#[test]
fn even_and_odd_call_each_other_at_every_width() {
    for w in WIDTHS {
        let exe = build(&format!("call-parity-{w}"), &module(&[parity_text(w)]));
        let inputs = if w == 1 { vec![0, -1] } else { small(w, 0) };
        for n in inputs {
            let even = n.rem_euclid(2) == 0;
            run(&exe, "even", w, n, &spell(1, -i128::from(even)));
            run(&exe, "odd", w, n, &spell(1, -i128::from(!even)));
        }
    }
}

#[test]
fn a_call_with_no_result_runs_and_the_caller_s_values_survive_it() {
    for w in WIDTHS {
        let t = format!("i{w}");
        let text = format!(
            "func @nothing() {{
^entry:
  ret @0
}}

func @sink(%x: {t}, %y: {t}) {{
^entry:
  %a: {t} = add %x, %y @0
  %b: {t} = mul %a, %a @0
  ret @0
}}

func @keep(%a: {t}, %b: {t}) -> {t} {{
^entry:
  %s: {t} = add %a, %b @0
  call @sink %s, %b @0
  call @nothing @0
  call @sink %b, %b @0
  %d: {t} = sub %s, %b @0
  ret %d @0
}}
"
        );
        let exe = build(&format!("call-none-{w}"), &module(&[text]));
        expect(&exe, &["@nothing"], &[]);
        for &a in &boundaries(w) {
            for &b in &boundaries(w) {
                let (a, b) = (spell(w, a), spell(w, b));
                expect(&exe, &["@sink", &a, &b], &[]);
                expect(&exe, &["@keep", &a, &b], &[&a]);
            }
        }
    }
}

#[test]
fn a_callee_whose_name_is_not_a_word_is_called_by_its_symbol() {
    for w in WIDTHS {
        let (t, one) = (format!("i{w}"), spell(w, 1));
        let text = format!(
            "func @\"1\"(%x: {t}) -> {t} {{
^entry:
  %one: {t} = const {one} @0
  %y: {t} = add %x, %one @0
  ret %y @0
}}

func @_end(%x: {t}) -> {t} {{
^entry:
  %y: {t} = call @\"1\" %x @0
  ret %y @0
}}

func @\"a b\"(%x: {t}) -> {t} {{
^entry:
  %y: {t} = call @_end %x @0
  %z: {t} = call @\"1\" %y @0
  ret %z @0
}}
"
        );
        let exe = build(&format!("call-names-{w}"), &module(&[text]));
        for v in boundaries(w) {
            let s = spell(w, v);
            expect(&exe, &["@\"1\"", &s], &[&spell(w, wrap(w, v + 1))]);
            expect(&exe, &["@_end", &s], &[&spell(w, wrap(w, v + 1))]);
            expect(&exe, &["@\"a b\"", &s], &[&spell(w, wrap(w, v + 2))]);
        }
    }
}
