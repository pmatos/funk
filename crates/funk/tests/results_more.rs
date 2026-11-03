//! Several results natively (#31, ADR-2026-11-03-0109): mixed widths in one
//! list of results, calls with six or more arguments whose results go in
//! memory, so that the result area's address pushes an argument onto the
//! stack, and direct and mutual recursion that returns several values at
//! every width the backend lowers. Recursion stays at most 20 deep.

mod common;

use common::{boundaries, build, expect, module, spell, wrap};
use funk_x86_64::width::SUPPORTED as WIDTHS;

/// `@mixed` returns seven results of five widths, in memory: `e`, `!a`
/// (`a + true`, whose slot holds 2 for `true`), `c - 1`, `b + 1`, `d`, `a`
/// and `e`. `@flip` returns two of other widths in registers. `@mixed_use`
/// passes two results of `@mixed` on to `@flip`, compares one, extends
/// another and adds it to a third.
const MIXED: &str = "func @mixed(%a: i1, %b: i8, %c: i16, %d: i32, %e: i64) -> i64, i1, i16, i8, i32, i1, i64 {
^entry:
  %t: i1 = const true @0
  %na: i1 = add %a, %t @0
  %one: i8 = const 1 @0
  %b1: i8 = add %b, %one @0
  %m: i16 = const -1 @0
  %c1: i16 = add %c, %m @0
  ret %e, %na, %c1, %b1, %d, %a, %e @0
}

func @flip(%x: i16, %y: i1) -> i1, i16 {
^entry:
  ret %y, %x @0
}

func @mixed_use(%a: i1, %b: i8, %c: i16, %d: i32, %e: i64) -> i8, i1, i16, i64, i1 {
^entry:
  %r0: i64, %r1: i1, %r2: i16, %r3: i8, %r4: i32, %r5: i1, %r6: i64 = call @mixed %a, %b, %c, %d, %e @0
  %f0: i1, %f1: i16 = call @flip %r2, %r1 @0
  %zero: i8 = const 0 @0
  %neg: i1 = icmp slt %r3, %zero @0
  %w: i64 = sext %r4 @0
  %sum: i64 = add %w, %r6 @0
  ret %r3, %neg, %f1, %sum, %f0 @0
}
";

/// The widths of `@mixed`'s parameters.
const MIXED_WIDTHS: [u32; 5] = [1, 8, 16, 32, 64];

/// The values of `iW` for each width of `widths`: the boundary values,
/// rotated by `r`.
fn rotated(widths: &[u32], r: usize) -> Vec<i128> {
    widths
        .iter()
        .enumerate()
        .map(|(k, &w)| {
            let b = boundaries(w);
            b[(k + r) % b.len()]
        })
        .collect()
}

fn line(func: &str, widths: &[u32], values: &[i128]) -> Vec<String> {
    let mut out = vec![func.to_string()];
    out.extend(
        widths
            .iter()
            .zip(values)
            .map(|(&w, &v)| spell(w, wrap(w, v))),
    );
    out
}

fn check(exe: &std::path::Path, args: &[String], want: &[String]) {
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    let want: Vec<&str> = want.iter().map(String::as_str).collect();
    expect(exe, &args, &want);
}

#[test]
fn results_of_mixed_widths_come_back_in_order() {
    let exe = build("results-mixed", &module(&[MIXED.to_string()]));
    for r in 0..5 {
        let p = rotated(&MIXED_WIDTHS, r);
        let (a, b, c, d, e) = (p[0], p[1], p[2], p[3], p[4]);
        let args = line("@mixed", &MIXED_WIDTHS, &p);
        let want = line(
            "",
            &[64, 1, 16, 8, 32, 1, 64],
            &[e, a + 1, c - 1, b + 1, d, a, e],
        );
        check(&exe, &args, &want[1..]);
        let b1 = wrap(8, b + 1);
        let want = line(
            "",
            &[8, 1, 16, 64, 1],
            &[b1, -i128::from(b1 < 0), c - 1, d + e, a + 1],
        );
        let args = line("@mixed_use", &MIXED_WIDTHS, &p);
        check(&exe, &args, &want[1..]);
    }
}

/// `@spread` takes eight arguments of the widths of `SPREAD` and returns
/// five results, in memory, so the area's address goes in `%rdi` and three
/// arguments go on the stack. `@six` takes six, the sixth of them then on
/// the stack, and `@six_call` passes results of one call to the next.
fn many_text() -> String {
    let params = |widths: &[u32]| -> String {
        let p: Vec<String> = widths
            .iter()
            .enumerate()
            .map(|(k, w)| format!("%p{k}: i{w}"))
            .collect();
        p.join(", ")
    };
    let (spread, six) = (params(&SPREAD), params(&SIX));
    let args = |n: usize| {
        (0..n)
            .map(|k| format!("%p{k}"))
            .collect::<Vec<_>>()
            .join(", ")
    };
    format!(
        "func @spread({spread}) -> i16, i8, i1, i64, i32 {{
^entry:
  %c8: i8 = const 1 @0
  %c16: i16 = const 1 @0
  %c64: i64 = const 1 @0
  %q7: i16 = add %p7, %c16 @0
  %q6: i8 = add %p6, %c8 @0
  %q4: i64 = add %p4, %c64 @0
  ret %q7, %q6, %p5, %q4, %p3 @0
}}

func @spread_call({spread}) -> i32, i64, i1, i8, i16 {{
^entry:
  %r0: i16, %r1: i8, %r2: i1, %r3: i64, %r4: i32 = call @spread {} @0
  ret %r4, %r3, %r2, %r1, %r0 @0
}}

func @six({six}) -> i64, i8, i1 {{
^entry:
  ret %p5, %p0, %p4 @0
}}

func @six_call({six}) -> i1, i64, i8, i64 {{
^entry:
  %a: i64, %b: i8, %c: i1 = call @six {} @0
  %d: i64, %e: i8, %f: i1 = call @six %b, %p1, %p2, %a, %c, %p3 @0
  ret %f, %d, %e, %a @0
}}
",
        args(8),
        args(6)
    )
}

const SPREAD: [u32; 8] = [1, 8, 16, 32, 64, 1, 8, 16];
const SIX: [u32; 6] = [8, 16, 32, 64, 1, 64];

#[test]
fn calls_of_six_and_more_arguments_return_results_in_memory() {
    let exe = build("results-many", &module(&[many_text()]));
    for r in 0..5 {
        let p = rotated(&SPREAD, r);
        let want = line(
            "",
            &[16, 8, 1, 64, 32],
            &[p[7] + 1, p[6] + 1, p[5], p[4] + 1, p[3]],
        );
        check(&exe, &line("@spread", &SPREAD, &p), &want[1..]);
        let want = line(
            "",
            &[32, 64, 1, 8, 16],
            &[p[3], p[4] + 1, p[5], p[6] + 1, p[7] + 1],
        );
        check(&exe, &line("@spread_call", &SPREAD, &p), &want[1..]);
        let q = rotated(&SIX, r);
        let want = line("", &[64, 8, 1], &[q[5], q[0], q[4]]);
        check(&exe, &line("@six", &SIX, &q), &want[1..]);
        let want = line("", &[1, 64, 8, 64], &[q[4], q[3], q[0], q[5]]);
        check(&exe, &line("@six_call", &SIX, &q), &want[1..]);
    }
}

/// `@fibs_W` returns two consecutive Fibonacci numbers, in registers;
/// `@trib_W` three consecutive Tribonacci numbers, in memory; `@even_W`
/// and `@odd_W` call each other and return whether `n` is even or odd,
/// `n` and `2n`.
fn recursion_text(w: u32) -> String {
    let t = format!("i{w}");
    let (zero, one, two) = (spell(w, 0), spell(w, 1), spell(w, 2));
    let half = |name: &str, other: &str, at_zero: &str| {
        format!(
            "func @{name}_{w}(%n: {t}) -> i1, {t}, {t} {{
^entry:
  %zero: {t} = const {zero} @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^stop, ^more @0
^stop:
  %r: i1 = const {at_zero} @0
  ret %r, %zero, %zero @0
^more:
  %one: {t} = const {one} @0
  %m: {t} = sub %n, %one @0
  %p: i1, %k: {t}, %d: {t} = call @{other}_{w} %m @0
  %k1: {t} = add %k, %one @0
  %two: {t} = const {two} @0
  %d2: {t} = add %d, %two @0
  ret %p, %k1, %d2 @0
}}
"
        )
    };
    format!(
        "func @fibs_{w}(%n: {t}) -> {t}, {t} {{
^entry:
  %zero: {t} = const {zero} @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^base, ^rec @0
^base:
  %one: {t} = const {one} @0
  ret %zero, %one @0
^rec:
  %one1: {t} = const {one} @0
  %m: {t} = sub %n, %one1 @0
  %a: {t}, %b: {t} = call @fibs_{w} %m @0
  %s: {t} = add %a, %b @0
  ret %b, %s @0
}}

func @trib_{w}(%n: {t}) -> {t}, {t}, {t} {{
^entry:
  %zero: {t} = const {zero} @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^base, ^rec @0
^base:
  %one: {t} = const {one} @0
  ret %zero, %zero, %one @0
^rec:
  %one1: {t} = const {one} @0
  %m: {t} = sub %n, %one1 @0
  %a: {t}, %b: {t}, %c: {t} = call @trib_{w} %m @0
  %ab: {t} = add %a, %b @0
  %s: {t} = add %ab, %c @0
  ret %b, %c, %s @0
}}

{}
{}",
        half("even", "odd", "true"),
        half("odd", "even", "false")
    )
}

/// The counts to recurse on at `iW`, at most 20, spelled as `iW` values.
fn counts(w: u32) -> Vec<i128> {
    if w == 1 {
        return vec![0, 1];
    }
    vec![0, 1, 2, 3, 5, 7, 10, 12, 13, 15, 16, 17, 20]
}

fn sequence(n: i128, start: &[i128]) -> Vec<i128> {
    let mut v = start.to_vec();
    while (v.len() as i128) < n + start.len() as i128 {
        let k = v.len();
        v.push(v[k - start.len()..].iter().sum());
    }
    v
}

#[test]
fn direct_and_mutual_recursion_return_several_values_at_every_width() {
    for w in WIDTHS {
        let exe = build(&format!("results-rec-{w}"), &module(&[recursion_text(w)]));
        let s = |v: i128| spell(w, wrap(w, v));
        for n in counts(w) {
            let arg = s(n);
            let fib = sequence(n, &[0, 1]);
            let f = (n as usize, n as usize + 1);
            expect(
                &exe,
                &[&format!("@fibs_{w}"), &arg],
                &[&s(fib[f.0]), &s(fib[f.1])],
            );
            let trib = sequence(n, &[0, 0, 1]);
            let t: Vec<String> = trib[n as usize..].iter().map(|&v| s(v)).collect();
            let t: Vec<&str> = t.iter().map(String::as_str).collect();
            expect(&exe, &[&format!("@trib_{w}"), &arg], &t);
            let even = spell(1, -i128::from(n % 2 == 0));
            let odd = spell(1, -i128::from(n % 2 == 1));
            expect(
                &exe,
                &[&format!("@even_{w}"), &arg],
                &[&even, &s(n), &s(2 * n)],
            );
            expect(
                &exe,
                &[&format!("@odd_{w}"), &arg],
                &[&odd, &s(n), &s(2 * n)],
            );
        }
    }
}
