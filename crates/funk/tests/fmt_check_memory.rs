//! `funk fmt --check` needs memory linear in its input, not in the
//! canonical text (#51): the canonical text of nested regions grows with
//! the square of their depth (`docs/decisions/rust-ir-and-tools.md#nesting`),
//! so a small file that is not canonical can have a canonical text far
//! larger than any memory budget, and it still gets its verdict
//! (`docs/decisions/rust-ir-and-tools-funk.md#funk-fmt`).

#![cfg(unix)]

mod common;

use std::process::{Command, Output};

use common::{file, text};
use funk_ir::{Registry, parse, print};

/// Levels of nested regions in the test's file.
const DEPTH: usize = 20_000;

/// The memory the run may map, in KiB: 256 MiB of data, and 16 MiB more of
/// address space.
const BUDGET_KIB: usize = 256 * 1024;

/// A module whose function nests `d` regions, each `ret` holding the next,
/// with no indentation, so it is not canonical from its third line on.
fn nested(d: usize) -> String {
    format!(
        "func @f() {{\n^e:\n{}ret @0\n{}}}\n\nlocs {{\n  @0 = unknown\n}}\n",
        "ret {\n^e:\n".repeat(d),
        "} @0\n".repeat(d)
    )
}

/// The size of the canonical text of `nested(d)`: level `k` from 0 adds
/// three lines indented `2 + 4k` or `4 + 4k` spaces.
fn canonical_len(d: usize) -> usize {
    6 * d * d + 21 * d + 52
}

/// Runs funk with `args`, its data limited to the budget and its address
/// space to 16 MiB more.
fn funk_on_budget(args: &[&str]) -> Output {
    let limits = format!(
        "ulimit -d {BUDGET_KIB} && ulimit -v {}",
        BUDGET_KIB + 16 * 1024
    );
    Command::new("sh")
        .arg("-c")
        .arg(format!("{limits} && exec \"$0\" \"$@\""))
        .arg(env!("CARGO_BIN_EXE_funk"))
        .args(args)
        .output()
        .expect("sh runs funk")
}

/// Removes the test's file when it ends, passed or failed.
struct Removed(String);

impl Drop for Removed {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

#[test]
fn canonical_len_is_the_size_of_the_printed_text() {
    let reg = Registry::core();
    for d in 0..40 {
        let m = parse(&nested(d), &reg).unwrap();
        assert_eq!(print(&m).len(), canonical_len(d), "depth {d}");
    }
}

#[test]
fn check_gives_a_verdict_when_the_canonical_text_exceeds_the_budget() {
    let input = nested(DEPTH);
    assert!(input.len() < 400_000, "{}", input.len());
    assert!(canonical_len(DEPTH) > 8 * BUDGET_KIB * 1024);
    let path = Removed(file("fmt-check-memory.fir", &input));

    let out = funk_on_budget(&["fmt", "--check", &path.0]);
    assert_eq!(out.status.code(), Some(1), "{}", text(&out.stderr));
    assert_eq!(text(&out.stdout), format!("{}\n", path.0));
    assert_eq!(text(&out.stderr), "");

    let out = funk_on_budget(&["fmt", "--check", "--json", &path.0]);
    assert_eq!(out.status.code(), Some(1), "{}", text(&out.stderr));
    let json = text(&out.stdout);
    assert!(json.contains(r#""verdict":"accepted""#), "{json}");
    assert!(json.ends_with("\"canonical\":false}\n"), "{json}");
}
