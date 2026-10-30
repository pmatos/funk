//! Functions that `funk build` compiles run natively: parameters, `const`
//! and `add` at every width the backend lowers, parameters on the stack, and
//! functions with no result (ADR-2026-10-30-1233).

mod common;

use common::{build, expect, func, module};
use funk_x86_64::width::SUPPORTED as WIDTHS;

/// The boundary values of `iW`, read as signed integers: 0, 1, -1, the
/// minimum and the maximum, or at `i1` `false` (0) and `true` (-1).
fn boundaries(w: u32) -> Vec<i128> {
    if w == 1 {
        return vec![0, -1];
    }
    let min = -(1i128 << (w - 1));
    vec![0, 1, -1, min, -min - 1]
}

/// The spelling of a value of `iW` in fir and on the command line.
fn spell(w: u32, v: i128) -> String {
    match (w, v & 1) {
        (1, 1) => "true".into(),
        (1, _) => "false".into(),
        _ => v.to_string(),
    }
}

/// `a + b` wrapped to `w` bits, read as signed.
fn wrapping_add(w: u32, a: i128, b: i128) -> i128 {
    let m = 1i128 << w;
    let s = (a + b).rem_euclid(m);
    if s >= m / 2 { s - m } else { s }
}

#[test]
fn parameters_constants_and_add_run_at_every_width() {
    for w in WIDTHS {
        let t = format!("i{w}");
        let vals = boundaries(w);
        let add = format!("%s: {t} = add %a, %b");
        let one = format!("%one: {t} = const {}", spell(w, 1));
        let inc = format!("%y: {t} = add %x, %one");
        let mut funcs = vec![
            func("id", &format!("%x: {t}"), &t, &["ret %x"]),
            func("add", &format!("%a: {t}, %b: {t}"), &t, &[&add, "ret %s"]),
            func("inc", &format!("%x: {t}"), &t, &[&one, &inc, "ret %y"]),
        ];
        for (k, v) in vals.iter().enumerate() {
            let c = format!("%c: {t} = const {}", spell(w, *v));
            funcs.push(func(&format!("c{k}"), "", &t, &[&c, "ret %c"]));
        }
        let exe = build(&format!("width-{w}"), &module(&funcs));
        for (k, &v) in vals.iter().enumerate() {
            let s = spell(w, v);
            expect(&exe, &["@id", &s], &[&s]);
            expect(&exe, &[&format!("@c{k}")], &[&s]);
            expect(&exe, &["@inc", &s], &[&spell(w, wrapping_add(w, v, 1))]);
            for &u in &vals {
                let sum = spell(w, wrapping_add(w, v, u));
                expect(&exe, &["@add", &s, &spell(w, u)], &[&sum]);
            }
        }
    }
}

#[test]
fn a_function_with_no_result_returns_an_empty_list() {
    let exe = build(
        "none",
        &module(&[
            func("none", "", "", &["ret"]),
            func("unused", "%x: i64", "", &["%y: i64 = add %x, %x", "ret"]),
            func(
                "ignored",
                "%a: i1, %b: i8, %c: i16, %d: i32, %e: i64, %f: i8, %g: i16",
                "",
                &["ret"],
            ),
        ]),
    );
    expect(&exe, &["@none"], &[]);
    expect(&exe, &["@unused", "-9223372036854775808"], &[]);
    expect(
        &exe,
        &["@ignored", "true", "1", "2", "3", "4", "5", "6"],
        &[],
    );
}

#[test]
fn parameters_past_the_sixth_arrive_on_the_stack() {
    let types = ["i1", "i8", "i16", "i32", "i64"];
    let args = [
        "true",
        "-100",
        "-30000",
        "-2000000000",
        "-9000000000000000000",
        "false",
        "100",
        "30000",
        "2000000000",
        "9000000000000000000",
    ];
    for n in 6..=10 {
        let params: Vec<String> = (0..n).map(|j| format!("%a{j}: {}", types[j % 5])).collect();
        let params = params.join(", ");
        let funcs: Vec<String> = (0..n)
            .map(|j| {
                func(
                    &format!("pick{j}"),
                    &params,
                    types[j % 5],
                    &[&format!("ret %a{j}")],
                )
            })
            .collect();
        let exe = build(&format!("stack-{n}"), &module(&funcs));
        for (j, want) in args.iter().enumerate().take(n) {
            let mut argv = vec![format!("@pick{j}")];
            argv.extend(args[..n].iter().map(|a| a.to_string()));
            let argv: Vec<&str> = argv.iter().map(String::as_str).collect();
            expect(&exe, &argv, &[want]);
        }
    }
    let params: Vec<String> = (0..9).map(|j| format!("%a{j}: i64")).collect();
    let sum = func(
        "sum",
        &params.join(", "),
        "i64",
        &["%s: i64 = add %a6, %a8", "%t: i64 = add %s, %a0", "ret %t"],
    );
    let exe = build("stack-sum", &module(&[sum]));
    expect(
        &exe,
        &["@sum", "1", "0", "0", "0", "0", "0", "20", "0", "300"],
        &["321"],
    );
}

/// The canonical text `tests/fir/canonical/NAME.fir`.
fn corpus(name: &str) -> String {
    let path = format!(
        "{}/../../tests/fir/canonical/{name}.fir",
        env!("CARGO_MANIFEST_DIR")
    );
    std::fs::read_to_string(path).unwrap()
}

#[test]
fn the_shared_corpus_builds_and_runs() {
    let exe = build("corpus-add", &corpus("add"));
    expect(&exe, &["@add3", "1", "2", "3"], &["6"]);
    expect(&exe, &["@add3", "2147483647", "1", "0"], &["-2147483648"]);
    expect(
        &exe,
        &["@double", "-4611686018427387905"],
        &["9223372036854775806"],
    );
    let exe = build("corpus-seven", &corpus("seven"));
    expect(&exe, &["@seven"], &["7"]);
    let exe = build("corpus-names", &corpus("names"));
    expect(&exe, &["@names", "1", "2", "3"], &["105"]);
    expect(&exe, &["@names", "127", "1", "0"], &["-29"]);
    let exe = build("corpus-locations", &corpus("locations"));
    expect(&exe, &["@f", "3"], &["45"]);
    let exe = build("corpus-symbols", &corpus("symbols"));
    for name in [
        r#"@"1""#,
        r#"@"a b""#,
        r#"@"""#,
        r#"@"_ZN3foo$LT$E""#,
        r#"@"tab\tquote\"slash\\line\n""#,
        r#"@"\u{202e}hidden\u{85}\u{feff}\u{1}""#,
        r#"@"résumé""#,
        "@_start.v2",
    ] {
        expect(&exe, &[name], &[]);
    }
}

#[test]
fn names_that_the_toolchain_uses_are_still_functions() {
    let names = [
        "_end",
        "_edata",
        "__bss_start",
        "_GLOBAL_OFFSET_TABLE_",
        "__tls_get_addr",
        "_start",
        "__funk_start",
        "etext",
        "end",
        "main",
    ];
    let funcs: Vec<String> = names
        .iter()
        .enumerate()
        .map(|(k, n)| func(n, "", "i8", &[&format!("%c: i8 = const {k}"), "ret %c"]))
        .collect();
    let exe = build("toolchain-names", &module(&funcs));
    for (k, n) in names.iter().enumerate() {
        expect(&exe, &[&format!("@{n}")], &[&k.to_string()]);
    }
}
