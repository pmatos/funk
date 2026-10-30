//! Round trips on the shared texts of `tests/fir/`.

mod common;

use common::{fir_files, parse_ok};
use funk_ir::{Registry, print, verify};

#[test]
fn canonical_texts_print_back_byte_for_byte() {
    for (name, text) in fir_files("canonical") {
        let m = parse_ok(&text);
        assert_eq!(print(&m), text, "{name}");
        assert_eq!(parse_ok(&print(&m)), m, "{name}");
    }
}

#[test]
fn canonical_texts_are_valid() {
    let reg = Registry::core();
    for (name, text) in fir_files("canonical") {
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
    for (name, text) in fir_files("canonical") {
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
