//! Round trips on the shared texts of `tests/fir/`, read with the dialects
//! that `funk` reads: the core and `gpu` (ADR-2026-11-09-1545).

mod common;

use common::fir_files;
use funk_ir::dialects::in_tree;
use funk_ir::{Module, parse, print, verify};

/// Parses with the core and `gpu`, or fails the test. `common::parse_ok`
/// reads the core alone, for the tests of the core's own texts.
fn parse_ok(text: &str) -> Module {
    parse(text, &in_tree()).unwrap_or_else(|e| panic!("{e}\n{text}"))
}

/// The canonical texts: those of `canonical/`, and the modules ported from
/// LLVM's tests, in `llvm/` (ADR-2026-11-03-0643).
fn canonical_texts() -> Vec<(String, String)> {
    let mut texts = fir_files("canonical");
    let ported = fir_files("llvm").into_iter();
    texts.extend(ported.map(|(name, text)| (format!("llvm/{name}"), text)));
    texts
}

#[test]
fn canonical_texts_print_back_byte_for_byte() {
    for (name, text) in canonical_texts() {
        let m = parse_ok(&text);
        assert_eq!(print(&m), text, "{name}");
        assert_eq!(parse_ok(&print(&m)), m, "{name}");
    }
}

#[test]
fn canonical_texts_are_valid() {
    let reg = in_tree();
    for (name, text) in canonical_texts() {
        let ds = verify(&parse_ok(&text), &reg);
        assert!(ds.is_empty(), "{name}: {ds:#?}");
    }
}

#[test]
fn noncanonical_inputs_parse_to_their_canonical_form() {
    let canonical: std::collections::HashMap<String, String> =
        fir_files("canonical").into_iter().collect();
    for (name, text) in fir_files("noncanonical") {
        let expected = canonical
            .get(&name)
            .unwrap_or_else(|| panic!("canonical/{name} exists"));
        assert_ne!(&text, expected, "{name} is not canonical");
        assert_eq!(parse_ok(&text), parse_ok(expected), "{name}");
        assert_eq!(&print(&parse_ok(&text)), expected, "{name}");
    }
}

/// Layouts that the repository's hooks keep out of committed files.
#[test]
fn layouts_the_hooks_forbid_parse_to_the_same_module() {
    for (name, text) in canonical_texts() {
        let m = parse_ok(&text);
        let variants = [
            text.trim_end_matches('\n').to_string(),
            text.replace('\n', "  \n"),
            text.replace('\n', "\t\n") + "\n\n",
            format!("{}// a comment at the very end, with no line feed", text),
        ];
        for v in variants {
            assert_eq!(parse_ok(&v), m, "{name}: {v:?}");
        }
    }
}
