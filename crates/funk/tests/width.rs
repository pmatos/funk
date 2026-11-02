//! `zext`, `sext` and `trunc` (#17): `funk verify`'s verdicts on width
//! changes, and native runs at every pair of the widths the backend lowers
//! that validation admits, on the boundary values of the operand's width.
//! A value of `iM` is the low `M` bits of its slot, and the bits above are
//! unspecified (ADR-2026-10-30-1231), so each change also runs on an
//! operand that `add` computed, whose slot holds other bits above `M` than
//! an argument's.

mod common;

use common::{boundaries, build, expect, file, func, funk, module, spell, text, wrap};
use funk_ir::dialects::core::WIDTH_CHANGES;
use funk_x86_64::width::SUPPORTED as WIDTHS;

/// The result of `op` from `iM` to `iN` on `v`, a value of `iM` read as
/// signed, read as signed at `iN`. `zext` keeps the unsigned value, `sext`
/// the signed one, and `trunc` the low `N` bits, which is the signed value
/// wrapped to `N` bits.
fn changed(op: &str, m: u32, n: u32, v: i128) -> i128 {
    match op {
        "zext" => wrap(n, v.rem_euclid(1 << m)),
        "sext" | "trunc" => wrap(n, v),
        _ => panic!("no width change {op}"),
    }
}

#[test]
fn the_results_are_those_that_lean_gives() {
    // `#guard`s of `lean/Fir/Core/Width.lean` (#66). Lean writes a result
    // as a natural number or a negative one; here it is wrapped to `N`.
    let min = |w: u32| -(1i128 << (w - 1));
    let max = |w: u32| (1i128 << (w - 1)) - 1;
    for (op, m, n, v, lean) in [
        ("zext", 1, 8, -1, 1),
        ("sext", 1, 8, -1, -1),
        ("zext", 1, 64, 0, 0),
        ("sext", 1, 64, 0, 0),
        ("zext", 8, 32, 0, 0),
        ("sext", 8, 32, 1, 1),
        ("zext", 8, 32, -1, 255),
        ("sext", 8, 32, -1, -1),
        ("zext", 8, 64, min(8), 128),
        ("sext", 8, 64, min(8), -128),
        ("zext", 8, 9, max(8), 127),
        ("sext", 8, 9, max(8), 127),
        ("zext", 7, 8, min(7), 64),
        ("sext", 7, 8, min(7), -64),
        ("sext", 7, 33, max(7), 63),
        ("zext", 33, 64, -1, 8_589_934_591),
        ("sext", 33, 64, min(33), -4_294_967_296),
        ("trunc", 8, 1, 2, 0),
        ("trunc", 8, 1, -1, 1),
        ("trunc", 64, 1, min(64), 0),
        ("trunc", 8, 7, max(8), -1),
        ("trunc", 8, 7, 64, -64),
        ("trunc", 33, 7, min(33), 0),
        ("trunc", 33, 8, -1, -1),
        ("trunc", 33, 32, max(33), -1),
        ("trunc", 64, 33, min(64), 0),
        ("trunc", 64, 33, max(64), -1),
    ] {
        assert_eq!(
            changed(op, m, n, v),
            wrap(n, lean),
            "{op} {v} from i{m} to i{n}"
        );
    }
}

/// Whether `op` may change `iM` to `iN`.
fn allowed(op: &str, m: u32, n: u32) -> bool {
    if op == "trunc" { n < m } else { m < n }
}

/// For each pair of the backend's widths that `op` may change, the
/// functions `@OP_M_N(%a: iM) -> iN`, which changes `%a`, and
/// `@OP_M_N_add(%a: iM, %b: iM) -> iN`, which changes `a + b`.
fn functions(op: &str) -> Vec<String> {
    let mut out = Vec::new();
    for m in WIDTHS {
        for n in WIDTHS.into_iter().filter(|&n| allowed(op, m, n)) {
            let (tm, tn) = (format!("i{m}"), format!("i{n}"));
            let change = format!("%r: {tn} = {op} %a");
            out.push(func(
                &format!("{op}_{m}_{n}"),
                &format!("%a: {tm}"),
                &tn,
                &[&change, "ret %r"],
            ));
            let sum = format!("%s: {tm} = add %a, %b");
            let change = format!("%r: {tn} = {op} %s");
            out.push(func(
                &format!("{op}_{m}_{n}_add"),
                &format!("%a: {tm}, %b: {tm}"),
                &tn,
                &[&sum, &change, "ret %r"],
            ));
        }
    }
    out
}

/// Builds every change of `op` between the backend's widths, and runs each
/// on every boundary value `v` of its operand's width: as an argument, and
/// as the sum of `v - k` and `k` for every boundary value `k`. Where that
/// sum wraps, as `max + 1` at `i8` does, the operand's slot holds bits
/// above `M` that an argument's does not: zeros above a set top bit, or
/// ones above a clear one.
fn runs_at_every_pair(op: &str) {
    let exe = build(&format!("width-{op}"), &module(&functions(op)));
    let mut pairs = 0;
    for m in WIDTHS {
        for n in WIDTHS.into_iter().filter(|&n| allowed(op, m, n)) {
            pairs += 1;
            let name = format!("@{op}_{m}_{n}");
            for v in boundaries(m) {
                let want = spell(n, changed(op, m, n, v));
                expect(&exe, &[&name, &spell(m, v)], &[&want]);
                for k in boundaries(m) {
                    let a = spell(m, wrap(m, v - k));
                    expect(&exe, &[&format!("{name}_add"), &a, &spell(m, k)], &[&want]);
                }
            }
        }
    }
    assert_eq!(pairs, 10, "{op}");
}

#[test]
fn zext_runs_at_every_pair_of_widths() {
    runs_at_every_pair("zext");
}

#[test]
fn sext_runs_at_every_pair_of_widths() {
    runs_at_every_pair("sext");
}

#[test]
fn trunc_runs_at_every_pair_of_widths() {
    runs_at_every_pair("trunc");
}

#[test]
fn sext_of_true_is_all_ones_and_zext_of_true_is_one() {
    let funcs: Vec<String> = WIDTHS[1..]
        .iter()
        .flat_map(|n| {
            ["zext", "sext"].map(|op| {
                let line = format!("%r: i{n} = {op} %a");
                func(
                    &format!("{op}{n}"),
                    "%a: i1",
                    &format!("i{n}"),
                    &[&line, "ret %r"],
                )
            })
        })
        .collect();
    let exe = build("width-true", &module(&funcs));
    for n in &WIDTHS[1..] {
        expect(&exe, &[&format!("@zext{n}"), "true"], &["1"]);
        expect(&exe, &[&format!("@sext{n}"), "true"], &["-1"]);
        expect(&exe, &[&format!("@zext{n}"), "false"], &["0"]);
        expect(&exe, &[&format!("@sext{n}"), "false"], &["0"]);
    }
}

/// A module whose function `@f` changes `%a: iM` to `iN` with `op`, at the
/// location `@1`.
fn change_module(op: &str, m: u32, n: u32, attrs: &str) -> String {
    format!(
        "func @f(%a: i{m}) -> i{n} {{\n^entry:\n  %r: i{n} = {op}{attrs} %a @1\n  ret %r @0\n}}\n\n\
         locs {{\n  @0 = unknown\n  @1 = \"w.c\":2:3 to 2:9\n}}\n"
    )
}

#[test]
fn verify_rejects_a_change_to_the_same_width_or_back_with_its_ir_location() {
    for op in WIDTH_CHANGES {
        for (m, n) in [(8, 8), (32, 32), (1, 1), (8, 32), (32, 8)] {
            if allowed(op, m, n) {
                continue;
            }
            let path = file(&format!("{op}-{m}-{n}.fir"), &change_module(op, m, n, ""));
            let out = funk(&["verify", "--json", &path], "");
            assert_eq!(out.status.code(), Some(1));
            let rule = if op == "trunc" {
                "strictly narrows, from iM to iN with N < M"
            } else {
                "strictly widens, from iM to iN with M < N"
            };
            let expected = format!(
                r#""verdict":"validation-error","diagnostics":[{{"kind":"validation-error","message":"{op} {rule}, not from i{m} to i{n}","func":"f","block":"entry","op":0,"loc":{{"ref":1,"location":"\"w.c\":2:3 to 2:9"}}}}]}}"#
            );
            let json = text(&out.stdout);
            assert!(json.ends_with(&format!("{expected}\n")), "{json}");
        }
    }
}

#[test]
fn verify_rejects_an_attribute_on_a_width_change_at_its_text_position() {
    for op in WIDTH_CHANGES {
        let (m, n) = if op == "trunc" { (32, 8) } else { (8, 32) };
        for attr in [" nuw", " nsw", " exact", " 1"] {
            let path = file(&format!("{op}-attr.fir"), &change_module(op, m, n, attr));
            let out = funk(&["verify", &path], "");
            assert_eq!(out.status.code(), Some(1));
            let err = text(&out.stderr);
            let col = if n < 10 { 12 } else { 13 };
            let head = format!(
                "{path}:3:{col}: parse error: op {op} does not decode: {op} takes no attributes"
            );
            assert!(err.starts_with(&head), "{err}");
        }
        let valid = file(&format!("{op}-valid.fir"), &change_module(op, m, n, ""));
        let out = funk(&["verify", &valid], "");
        assert_eq!(out.status.code(), Some(0), "{}", text(&out.stderr));
    }
}
