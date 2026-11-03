//! G0's check on the Rust side (ADR-2026-11-03-0600).
//!
//! `funk-ir` holds an op as data, a name and its parts, and learns what an
//! op means only from the [`Registry`]: there is no closed `enum` of ops,
//! and the IR, the parser, the printer and the verifier have no per-op code
//! (ADR-2026-10-29-2016, ADR-2026-10-30-1146). The tests check it two ways.
//! An empty registry knows no op, so nothing outside the registry knows
//! one. And the code of every module but the dialects and the module
//! generator writes no word of the core dialect's text, names the core
//! dialect only to register it, and declares no `enum` with a variant named
//! after a core op.

mod g0_scan;

use std::path::{Path, PathBuf};

use funk_ir::dialects::core::{self, PREDICATES, WRAP_FLAG_SETS};
use funk_ir::{Block, Func, LocRef, Location, Module, Op, Registry, parse, print, verify};
use g0_scan::{Tok, code, enum_variants, tokens};

/// The core dialect's op names, from its registration.
fn core_ops() -> Vec<String> {
    core::dialect()
        .ops
        .iter()
        .map(|op| op.name().to_string())
        .collect()
}

/// Every word of the core dialect's text, but the `iN` types, which
/// [`is_core_word`] matches by their form.
fn core_words() -> Vec<String> {
    let mut words = core_ops();
    words.extend(PREDICATES.iter().map(|p| p.to_string()));
    words.extend(
        WRAP_FLAG_SETS
            .iter()
            .flat_map(|s| s.iter().map(|f| f.to_string())),
    );
    // `sdiv exact`, the `i1` constants and the reserved `ptr`, which the
    // dialect does not export by name.
    words.extend(["exact", "true", "false", "ptr"].map(String::from));
    words.sort();
    words.dedup();
    words
}

/// Whether `s` is a word of the core dialect's text: one of `words`, or a
/// type `iN`.
fn is_core_word(words: &[String], s: &str) -> bool {
    let int = s
        .strip_prefix('i')
        .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()));
    int || words.iter().any(|w| w == s)
}

/// The variant name that an `enum` of core ops would give `word`:
/// `cond_br` gives `CondBr`.
fn camel(word: &str) -> String {
    word.split('_')
        .map(|part| {
            let mut cs = part.chars();
            cs.next()
                .map(|c| c.to_ascii_uppercase().to_string() + cs.as_str())
                .unwrap_or_default()
        })
        .collect()
}

/// The modules of `funk-ir` whose code sees every op alike: all of `src/`
/// but the dialects, which define ops, and the module generator, which
/// builds core modules for the property tests. A new module is checked
/// unless it goes in one of those places.
fn generic_sources() -> Vec<(String, String)> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut files = Vec::new();
    let mut dirs = vec![root.join("src")];
    while let Some(dir) = dirs.pop() {
        for entry in std::fs::read_dir(&dir).expect("a source directory") {
            let path = entry.expect("a directory entry").path();
            if path.is_dir() {
                dirs.push(path);
            } else if path.extension().is_some_and(|x| x == "rs") {
                files.push(path);
            }
        }
    }
    let rel = |p: &Path| -> String {
        let r = p.strip_prefix(&root).expect("under the crate");
        r.to_string_lossy().replace('\\', "/")
    };
    let mut out: Vec<(String, String)> = files
        .iter()
        .map(|p| (rel(p), p))
        .filter(|(r, _)| {
            !r.starts_with("src/dialects/")
                && r != "src/generate.rs"
                && !r.starts_with("src/generate/")
        })
        .map(|(r, p)| (r, std::fs::read_to_string(p).expect("a UTF-8 source")))
        .collect();
    out.sort();
    out
}

/// The text of a module with one function, `@f`, whose entry block holds
/// one op, `name`, with no parts.
fn bare_op_text(name: &str) -> String {
    format!("func @f() {{\n^entry:\n  {name} @0\n}}\n\nlocs {{\n  @0 = unknown\n}}\n")
}

/// That module, built.
fn bare_op_module(name: &str) -> Module {
    let mut m = Module::new();
    let here = m.locs.push(Location::Unknown);
    m.func(Func::new("f").block(Block::new("entry").op(Op::new(name, here))))
}

#[test]
fn an_op_is_a_name_and_its_parts() {
    // Built field by field, so this stops compiling if the name becomes
    // anything but a string or an op gains a part the spec does not have.
    let op = Op {
        results: vec![],
        name: String::from("gpu.launch"),
        attrs: vec![],
        operands: vec![],
        succs: vec![],
        regions: vec![],
        loc: LocRef(0),
    };
    let mut m = Module::new();
    m.locs.push(Location::Unknown);
    let m = m.func(Func::new("f").block(Block::new("entry").op(op)));
    assert_eq!(print(&m), bare_op_text("gpu.launch"));
    let ds = verify(&m, &Registry::core());
    let messages: Vec<&str> = ds.iter().map(|d| d.message.as_str()).collect();
    assert_eq!(messages, ["op gpu.launch is not registered"]);
}

#[test]
fn an_empty_registry_knows_no_op() {
    let none = Registry::new();
    for name in core_ops() {
        let text = bare_op_text(&name);
        let e = parse(&text, &none).expect_err("no op parses without its dialect");
        assert_eq!(e.reason, format!("unknown op {name}"), "{text}");
        let m = bare_op_module(&name);
        assert_eq!(print(&m), text);
        let ds = verify(&m, &none);
        let messages: Vec<&str> = ds.iter().map(|d| d.message.as_str()).collect();
        assert_eq!(messages, [format!("op {name} is not registered")]);
    }
}

#[test]
fn the_check_covers_the_ir_the_parser_the_printer_and_the_verifier() {
    let files: Vec<String> = generic_sources().into_iter().map(|(p, _)| p).collect();
    for want in [
        "src/lib.rs",
        "src/registry.rs",
        "src/ir/module.rs",
        "src/text/grammar.rs",
        "src/text/decode.rs",
        "src/text/print.rs",
        "src/verify/ops.rs",
    ] {
        assert!(files.iter().any(|f| f == want), "{want} is not checked");
    }
    assert!(files.iter().all(|f| !f.starts_with("src/dialects/")));
    assert!(core_ops().len() >= 24, "{:?}", core_ops());
    for w in ["add", "cond_br", "slt", "nsw", "exact", "true", "ptr"] {
        assert!(is_core_word(&core_words(), w), "{w}");
    }
    assert!(is_core_word(&core_words(), "i32") && !is_core_word(&core_words(), "i"));
}

#[test]
fn the_generic_modules_write_no_word_of_the_core_dialect() {
    let words = core_words();
    let mut found = Vec::new();
    for (path, src) in generic_sources() {
        for t in code(&tokens(&src)) {
            if let Tok::Str(s) = t
                && is_core_word(&words, &s)
            {
                found.push(format!("{path}: \"{s}\""));
            }
        }
    }
    assert!(
        found.is_empty(),
        "per-op code outside a dialect (ADR-2026-11-03-0600): {found:#?}"
    );
}

#[test]
fn only_the_registry_names_the_core_dialect() {
    let mut found = Vec::new();
    for (path, src) in generic_sources() {
        if path == "src/lib.rs" || path == "src/registry.rs" {
            continue;
        }
        let toks = code(&tokens(&src));
        if toks.iter().any(|t| *t == Tok::Ident("dialects".into())) {
            found.push(path);
        }
    }
    assert!(
        found.is_empty(),
        "only lib.rs declares the dialects and only the registry registers \
         the core dialect (ADR-2026-11-03-0600): {found:?}"
    );
}

#[test]
fn no_enum_has_a_variant_named_after_a_core_op() {
    let variants: Vec<String> = core_ops().iter().map(|w| camel(w)).collect();
    let mut found = Vec::new();
    for (path, src) in generic_sources() {
        for (name, v) in enum_variants(&code(&tokens(&src))) {
            if variants.contains(&v) {
                found.push(format!("{path}: {name}::{v}"));
            }
        }
    }
    assert!(
        found.is_empty(),
        "a closed enum of core ops outside a dialect (ADR-2026-11-03-0600): {found:?}"
    );
    assert_eq!(camel("cond_br"), "CondBr");
}
