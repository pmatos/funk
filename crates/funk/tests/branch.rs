//! `br` and `cond_br` (#19), run natively at every width the backend
//! lowers: block arguments that swap, rotate and pass one value to several
//! arguments on every trip round a loop, which the branch copies as one
//! parallel move (ADR-2026-10-31-0335), and conditions whose slots hold
//! bits above bit 0, which `cond_br` must not read (ADR-2026-10-30-1231).

mod common;

use std::path::Path;

use common::{boundaries, build, expect, module, spell, wrap};
use funk_x86_64::width::SUPPORTED as WIDTHS;

/// A loop at `iW` over `^loop(%x, %y, %z, %k: i8)` that passes `next`, the
/// three values in some order, while `%k` is above zero, counting `%k`
/// down, then returns `%x`, `%y` or `%z`: one function for each.
fn shuffle_texts(name: &str, w: u32, next: &str) -> Vec<String> {
    ["x", "y", "z"]
        .map(|out| {
            format!(
                "func @{name}_{out}_{w}(%a: i{w}, %b: i{w}, %c: i{w}, %n: i8) -> i{w} {{
^entry:
  br ^loop(%a, %b, %c, %n) @0
^loop(%x: i{w}, %y: i{w}, %z: i{w}, %k: i8):
  %zero: i8 = const 0 @0
  %more: i1 = icmp sgt %k, %zero @0
  %one: i8 = const 1 @0
  %k1: i8 = sub %k, %one @0
  cond_br %more, ^loop({next}, %k1), ^exit(%{out}) @0
^exit(%r: i{w}):
  ret %r @0
}}
"
            )
        })
        .to_vec()
}

/// How one trip round a loop changes `(x, y, z)`.
type Step = fn([i128; 3]) -> [i128; 3];

/// The loops of this file: each one's name, what its `br` passes, and the
/// model of that.
const SHUFFLES: [(&str, &str, Step); 4] = [
    ("swap", "%y, %x, %z", |[x, y, z]| [y, x, z]),
    ("rotate", "%y, %z, %x", |[x, y, z]| [y, z, x]),
    // Into x and y from x, so x's old value goes to two arguments.
    ("fan", "%x, %x, %y", |[x, y, _]| [x, x, y]),
    // z and x swap, and x's old value also goes to y.
    ("mix", "%z, %x, %x", |[x, _, z]| [z, x, x]),
];

#[test]
fn block_arguments_swap_rotate_and_fan_out_round_a_loop_at_every_width() {
    for w in WIDTHS {
        let texts: Vec<String> = SHUFFLES
            .iter()
            .flat_map(|(name, next, _)| shuffle_texts(name, w, next))
            .collect();
        let exe = build(&format!("branch-shuffle-{w}"), &module(&texts));
        let b = boundaries(w);
        let starts = [
            [b[0], b[b.len() - 1], b[1]],
            [b[b.len() - 1], b[0], b[0]],
            [wrap(w, 7), wrap(w, -3), wrap(w, 2)],
        ];
        for (name, _, step) in SHUFFLES {
            for start in starts {
                let mut state = start;
                for n in 0..7 {
                    for (i, out) in ["x", "y", "z"].iter().enumerate() {
                        let f = format!("@{name}_{out}_{w}");
                        let args = start.map(|v| spell(w, v));
                        let n = n.to_string();
                        let all = [f.as_str(), &args[0], &args[1], &args[2], &n];
                        expect(&exe, &all, &[&spell(w, state[i])]);
                    }
                    state = step(state);
                }
            }
        }
    }
}

/// `@pick(%c: i1, %a: iW, %b: iW) -> iW`: `cond_br` to `%a`'s block when
/// `%c` is true and `%b`'s when it is false, each passed as an argument.
fn pick_text(w: u32) -> String {
    format!(
        "func @pick_{w}(%c: i1, %a: i{w}, %b: i{w}) -> i{w} {{
^entry:
  cond_br %c, ^t(%a), ^e(%b) @0
^t(%x: i{w}):
  ret %x @0
^e(%y: i{w}):
  ret %y @0
}}
"
    )
}

#[test]
fn cond_br_goes_by_its_condition_at_every_width() {
    for w in WIDTHS {
        let exe = build(&format!("branch-pick-{w}"), &module(&[pick_text(w)]));
        for a in boundaries(w) {
            for b in boundaries(w) {
                for (c, want) in [("true", a), ("false", b)] {
                    let (f, a, b) = (format!("@pick_{w}"), spell(w, a), spell(w, b));
                    expect(&exe, &[&f, c, &a, &b], &[&spell(w, want)]);
                }
            }
        }
    }
}

/// `@low_M(%v: iM) -> i8`: 1 when bit 0 of `%v` is set, else 0, by a
/// `cond_br` on `trunc %v` to `i1`, whose slot holds all of `%v`'s bits.
/// `@sum1(%p: i1, %q: i1) -> i8` does the same on `%p + %q`, whose slot
/// holds 2 when both are `true`, and `@diff1` on `%p - %q`, which holds
/// -1 for `false - true`. The `i1` also passes through a block argument
/// before the second test, so the bits above bit 0 travel with it.
fn low_texts() -> Vec<String> {
    let tail = "  cond_br %c, ^one(%c), ^zero(%c) @0
^one(%x: i1):
  cond_br %x, ^t, ^e @0
^zero(%y: i1):
  cond_br %y, ^t, ^e @0
^t:
  %r1: i8 = const 1 @0
  ret %r1 @0
^e:
  %r0: i8 = const 0 @0
  ret %r0 @0
}
";
    let mut out: Vec<String> = [8, 16, 32, 64]
        .map(|m| {
            format!("func @low_{m}(%v: i{m}) -> i8 {{\n^entry:\n  %c: i1 = trunc %v @0\n{tail}")
        })
        .to_vec();
    for (name, op) in [("sum1", "add"), ("diff1", "sub")] {
        out.push(format!(
            "func @{name}(%p: i1, %q: i1) -> i8 {{\n^entry:\n  %c: i1 = {op} %p, %q @0\n{tail}"
        ));
    }
    out
}

/// Runs `@name` of `exe` on `args` and checks that it gives `bit`.
fn expect_bit(exe: &Path, name: &str, args: &[&str], bit: bool) {
    let mut all = vec![name];
    all.extend(args);
    expect(exe, &all, &[if bit { "1" } else { "0" }]);
}

#[test]
fn cond_br_reads_bit_0_of_its_condition_and_nothing_above() {
    let exe = build("branch-low", &module(&low_texts()));
    for m in [8u32, 16, 32, 64] {
        let min = -(1i128 << (m - 1));
        for v in [0, 1, 2, 3, -1, -2, min, -min - 1, 254, 256, 257] {
            let v = wrap(m, v);
            expect_bit(&exe, &format!("@low_{m}"), &[&v.to_string()], v & 1 == 1);
        }
    }
    for (p, q, sum, diff) in [
        ("true", "true", false, false),
        ("true", "false", true, true),
        ("false", "true", true, true),
        ("false", "false", false, false),
    ] {
        expect_bit(&exe, "@sum1", &[p, q], sum);
        expect_bit(&exe, "@diff1", &[p, q], diff);
    }
}
