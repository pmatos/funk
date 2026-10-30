//! funk needs no large stack (ADR-2026-10-30-1333): on texts nested a
//! million levels deep in attributes, regions and items, it gives its usual
//! verdicts with a main thread of 1 MiB, where a walk that recursed once per
//! level would overflow within a few thousand levels.

#![cfg(unix)]

mod common;

use std::process::{Command, Output};

use common::{file, text};

const DEPTH: usize = 1_000_000;

/// Runs funk with `args` and its stack limited to 1 MiB.
fn funk_on_small_stack(args: &[&str]) -> Output {
    Command::new("sh")
        .args(["-c", "ulimit -s 1024 && exec \"$0\" \"$@\""])
        .arg(env!("CARGO_BIN_EXE_funk"))
        .args(args)
        .output()
        .expect("sh runs funk")
}

/// Removes the test's files when it ends, passed or failed: they take
/// tens of megabytes.
struct Files(Vec<String>);

impl Drop for Files {
    fn drop(&mut self) {
        for path in &self.0 {
            let _ = std::fs::remove_file(path);
        }
    }
}

/// Asserts that each line of a JSON report is a parse error whose message
/// holds the matching reason.
fn parse_errors(out: &Output, reasons: &[&str]) {
    assert_eq!(out.status.code(), Some(1), "{}", text(&out.stderr));
    let stdout = text(&out.stdout);
    let reports: Vec<&str> = stdout.lines().collect();
    assert_eq!(reports.len(), reasons.len(), "{stdout}");
    for (report, reason) in reports.iter().zip(reasons) {
        assert!(report.contains(r#""verdict":"parse-error""#), "{report}");
        assert!(report.contains(reason), "{report}");
    }
}

#[test]
fn texts_nested_a_million_levels_deep_get_their_verdicts() {
    let module = |items: &str| format!("{items}\nlocs {{\n  @0 = unknown\n}}\n");
    let attrs = module(&format!(
        "func @f() {}x{} {{\n^e:\n  ret @0\n}}\n",
        "h(".repeat(DEPTH),
        ")".repeat(DEPTH)
    ));
    let regions = module(&format!(
        "func @f() {{\n^e:\n{}{}  ret @0\n}}\n",
        "toy.nest {\n^e:\n".repeat(DEPTH),
        "} @0\n".repeat(DEPTH)
    ));
    let items = module(&format!(
        "{}{}",
        "func @f() {\n".repeat(DEPTH),
        "}\n".repeat(DEPTH)
    ));
    let paths = Files(vec![
        file("deep-attrs.fir", &attrs),
        file("deep-regions.fir", &regions),
        file("deep-items.fir", &items),
    ]);
    let reasons = [
        "a func has no attributes",
        "unknown op toy.nest",
        "holds blocks, not items",
    ];
    let args: Vec<&str> = ["verify", "--json"]
        .into_iter()
        .chain(paths.0.iter().map(String::as_str))
        .collect();
    parse_errors(&funk_on_small_stack(&args), &reasons);
    let out = funk_on_small_stack(&["fmt", "--json", &paths.0[0]]);
    parse_errors(&out, &reasons[..1]);
}
