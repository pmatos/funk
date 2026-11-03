//! Functions and calls with any number of results (#31), run natively at
//! every width the backend lowers. One or two results come back in `%rax`
//! and `%rdx`, and more in a result area that the caller provides, whose
//! address the call passes first (ADR-2026-11-03-0109). Each caller here
//! uses every result of its calls and passes some on to another call, and
//! the executable prints every result, in order. Sums that wrap leave bits
//! above the width in their slots, such as 128 for `127 + 1` at `i8`, so
//! each reader must read only the low bits. `results_more.rs` has mixed
//! widths, calls with more than six arguments, and recursion.

mod common;

use common::{boundaries, build, expect, module, spell, wrap};
use funk_x86_64::width::SUPPORTED as WIDTHS;

/// The functions of one width `w`:
///
/// - `@none_W` returns nothing, and `@call_none_W` calls it and returns
///   its argument;
/// - `@two_W` returns `a + b` and `a`, in registers;
/// - `@three_W` returns `a - b`, `a + b` and `b`, in memory;
/// - `@eight_W` returns `a`, `a + 1`, ... `a + 7`;
/// - `@use_W` calls `@three_W`, passes two of its results on to `@two_W`
///   and one to `@eight_W`, and returns something of each call: `two`'s
///   first result, `eight`'s last and `three`'s last.
fn text(w: u32) -> String {
    let t = format!("i{w}");
    let one = spell(w, 1);
    let mut eight = format!(
        "func @eight_{w}(%a: {t}) -> {} {{\n^entry:\n",
        [t.as_str(); 8].join(", ")
    );
    eight += &format!("  %one: {t} = const {one} @0\n  %a0: {t} = add %a, %one @0\n");
    for k in 1..7 {
        eight += &format!("  %a{k}: {t} = add %a{}, %one @0\n", k - 1);
    }
    eight += "  ret %a, %a0, %a1, %a2, %a3, %a4, %a5, %a6 @0\n}\n";
    format!(
        "func @none_{w}(%a: {t}) {{
^entry:
  %b: {t} = add %a, %a @0
  ret @0
}}

func @call_none_{w}(%a: {t}) -> {t} {{
^entry:
  call @none_{w} %a @0
  ret %a @0
}}

func @two_{w}(%a: {t}, %b: {t}) -> {t}, {t} {{
^entry:
  %s: {t} = add %a, %b @0
  ret %s, %a @0
}}

func @three_{w}(%a: {t}, %b: {t}) -> {t}, {t}, {t} {{
^entry:
  %d: {t} = sub %a, %b @0
  %s: {t} = add %a, %b @0
  ret %d, %s, %b @0
}}

{eight}
func @use_{w}(%a: {t}, %b: {t}) -> {t}, {t}, {t} {{
^entry:
  %d: {t}, %s: {t}, %c: {t} = call @three_{w} %a, %b @0
  %x: {t}, %y: {t} = call @two_{w} %d, %s @0
  %e0: {t}, %e1: {t}, %e2: {t}, %e3: {t}, %e4: {t}, %e5: {t}, %e6: {t}, %e7: {t} = call @eight_{w} %y @0
  ret %x, %e7, %c @0
}}
"
    )
}

fn spelled(w: u32, values: &[i128]) -> Vec<String> {
    values.iter().map(|&v| spell(w, wrap(w, v))).collect()
}

fn check(exe: &std::path::Path, func: &str, w: u32, args: &[i128], want: &[i128]) {
    let args = spelled(w, args);
    let mut line = vec![format!("@{func}_{w}")];
    line.extend(args);
    let line: Vec<&str> = line.iter().map(String::as_str).collect();
    let want = spelled(w, want);
    let want: Vec<&str> = want.iter().map(String::as_str).collect();
    expect(exe, &line, &want);
}

#[test]
fn functions_return_none_one_two_three_and_eight_values_at_every_width() {
    for w in WIDTHS {
        let exe = build(&format!("results-{w}"), &module(&[text(w)]));
        for &a in &boundaries(w) {
            check(&exe, "none", w, &[a], &[]);
            check(&exe, "call_none", w, &[a], &[a]);
            check(
                &exe,
                "eight",
                w,
                &[a],
                &(0..8).map(|k| a + k).collect::<Vec<_>>(),
            );
            for &b in &boundaries(w) {
                check(&exe, "two", w, &[a, b], &[a + b, a]);
                check(&exe, "three", w, &[a, b], &[a - b, a + b, b]);
                let (d, s) = (a - b, a + b);
                let (x, y) = (d + s, d);
                check(&exe, "use", w, &[a, b], &[x, y + 7, b]);
            }
        }
    }
}

/// A function of no result prints an empty list, and one that ignores
/// some results of its call still reads the others.
#[test]
fn the_executable_prints_every_result_in_order() {
    let exe = build("results-order", &module(&[text(64)]));
    expect(&exe, &["@none_64", "5"], &[]);
    expect(&exe, &["@three_64", "7", "2"], &["5", "9", "2"]);
    expect(
        &exe,
        &["@eight_64", "9223372036854775806"],
        &[
            "9223372036854775806",
            "9223372036854775807",
            "-9223372036854775808",
            "-9223372036854775807",
            "-9223372036854775806",
            "-9223372036854775805",
            "-9223372036854775804",
            "-9223372036854775803",
        ],
    );
}
