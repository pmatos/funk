//! Helpers shared by the integration tests.

#![allow(dead_code)]

use std::path::PathBuf;

use funk_ir::{Diagnostic, Module, ParseError, Registry, parse, verify};

/// The directory of the shared fir test texts, `tests/fir/`.
pub fn fir_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests/fir")
}

/// The `.fir` files of a directory of `tests/fir/`, sorted by name.
pub fn fir_files(dir: &str) -> Vec<(String, String)> {
    let mut files: Vec<(String, String)> = std::fs::read_dir(fir_dir().join(dir))
        .expect("the corpus directory exists")
        .map(|e| e.expect("a directory entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "fir"))
        .map(|p| {
            let name = p.file_name().unwrap().to_string_lossy().into_owned();
            (name, std::fs::read_to_string(&p).expect("a UTF-8 text"))
        })
        .collect();
    files.sort();
    assert!(!files.is_empty(), "{dir} holds .fir files");
    files
}

/// Parses with the core dialect, or fails the test.
pub fn parse_ok(text: &str) -> Module {
    parse(text, &Registry::core()).unwrap_or_else(|e| panic!("{e}\n{text}"))
}

/// The parse error of a text that the core parser must reject.
pub fn parse_err(text: &str) -> ParseError {
    match parse(text, &Registry::core()) {
        Ok(m) => panic!("parsed a text it must reject:\n{text}\n{m:?}"),
        Err(e) => e,
    }
}

/// The diagnostics of a text that parses with the core dialect.
pub fn diagnostics(text: &str) -> Vec<Diagnostic> {
    verify(&parse_ok(text), &Registry::core())
}

/// Wraps the body of one function in a module whose table has `@0`.
pub fn one_func(func: &str) -> String {
    format!("{func}\nlocs {{\n  @0 = unknown\n}}\n")
}

/// Asserts that a text parses and is rejected only by a diagnostic whose
/// message holds `needle`.
pub fn rejects(text: &str, needle: &str) -> Vec<Diagnostic> {
    let ds = diagnostics(text);
    assert!(
        ds.iter().any(|d| d.message.contains(needle)),
        "expected a diagnostic with {needle:?}, got {ds:#?}\n{text}"
    );
    ds
}
