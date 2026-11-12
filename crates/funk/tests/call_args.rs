//! Calls with more than six arguments, of mixed widths, and the spec's
//! example module, run natively (#20).
//!
//! The arguments past the sixth go on the stack (ADR-2026-10-30-1232), and
//! no argument is extended
//! (`docs/decisions/x86-64-backend-abi.md#calls-between-funk-functions`):
//! each caller here passes the sum of a parameter and 1, whose slot holds
//! bits above the value's width where the sum wraps, such as 128 for
//! `127 + 1` at `i8`, and each callee reads only the low bits of the one
//! argument it returns.

mod common;

use common::{boundaries, build, expect, module, spell, wrap};
use funk_x86_64::width::ONE_REGISTER as WIDTHS;

/// The width of argument `i` of a call: the widths in turn.
fn width(i: usize) -> u32 {
    WIDTHS[i % WIDTHS.len()]
}

/// `@via_K_J`, which takes `k` parameters of the widths in turn, adds 1 to
/// each, and passes the sums in reverse order to `@pick_K_J`, which
/// returns its argument `j` extended by sign to `i64`.
fn pair_text(k: usize, j: usize) -> String {
    let mut via = String::new();
    let params: Vec<String> = (0..k).map(|i| format!("%p{i}: i{}", width(i))).collect();
    via += &format!(
        "func @via_{k}_{j}({}) -> i64 {{\n^entry:\n",
        params.join(", ")
    );
    for i in 0..k {
        let w = width(i);
        via += &format!("  %c{i}: i{w} = const {} @0\n", spell(w, 1));
        via += &format!("  %d{i}: i{w} = add %p{i}, %c{i} @0\n");
    }
    let args: Vec<String> = (0..k).rev().map(|i| format!("%d{i}")).collect();
    via += &format!(
        "  %r: i64 = call @pick_{k}_{j} {} @0\n  ret %r @0\n}}\n",
        args.join(", ")
    );
    let params: Vec<String> = (0..k)
        .map(|i| format!("%q{i}: i{}", width(k - 1 - i)))
        .collect();
    let mut pick = format!(
        "func @pick_{k}_{j}({}) -> i64 {{\n^entry:\n",
        params.join(", ")
    );
    if width(k - 1 - j) == 64 {
        pick += &format!("  ret %q{j} @0\n}}\n");
    } else {
        pick += &format!("  %s: i64 = sext %q{j} @0\n  ret %s @0\n}}\n");
    }
    via + "\n" + &pick
}

#[test]
fn calls_pass_more_than_six_arguments_of_mixed_widths() {
    let mut funcs = Vec::new();
    for k in 7..=12 {
        for j in 0..k {
            funcs.push(pair_text(k, j));
        }
    }
    let exe = build("call-args", &module(&funcs));
    for k in 7..=12 {
        for j in 0..k {
            for shift in 0..3 {
                let vals: Vec<i128> = (0..k)
                    .map(|i| {
                        let b = boundaries(width(i));
                        b[(i + shift) % b.len()]
                    })
                    .collect();
                let mut args = vec![format!("@via_{k}_{j}")];
                args.extend((0..k).map(|i| spell(width(i), vals[i])));
                let args: Vec<&str> = args.iter().map(String::as_str).collect();
                // `@pick`'s argument `j` is `@via`'s sum `k - 1 - j`.
                let from = k - 1 - j;
                let want = wrap(width(from), vals[from] + 1);
                expect(&exe, &args, &[&want.to_string()]);
            }
        }
    }
}

#[test]
fn the_spec_s_example_module_runs_and_sum10_gives_45() {
    // The text of `lean/Fir/Text/Example.lean`: `@sum10` calls `@sum`.
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

func @sum10() -> i32 {
^entry:
  %ten: i32 = const 10 @5
  %s: i32 = call @sum %ten @6
  ret %s @0
}

locs {
  @0 = unknown
  @1 = \"sum.c\":2:3 to 2:15
  @2 = \"sum.c\":3:10 to 3:16
  @3 = \"sum.c\":4:5 to 4:17
  @4 = \"sum.c\":6:3 to 6:14
  @5 = \"main.c\":2:19 to 2:21
  @6 = \"main.c\":2:15 to 2:22
}
";
    let exe = build("call-spec-sum", text);
    expect(&exe, &["@sum10"], &["45"]);
    for (n, want) in [("10", "45"), ("0", "0"), ("1", "0"), ("100", "4950")] {
        expect(&exe, &["@sum", n], &[want]);
    }
}
