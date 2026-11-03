//! G0's check on the Rust side (ADR-2026-11-03-0600).
//!
//! `funk-ir` holds an op as data, a name and its parts, and learns what an
//! op means only from the [`Registry`]: there is no closed `enum` of ops,
//! and the IR, the parser, the printer and the verifier have no per-op code
//! (ADR-2026-10-29-2016, ADR-2026-10-30-1146). The tests check it two ways.
//! An empty registry knows no op, so nothing outside the registry knows
//! one. And the code of every module but the dialects, the module generator
//! and the unit tests writes no word of the core dialect's text, names the
//! core dialect only to register it, and declares no `enum` with two or
//! more variants named after core ops.

mod g0_scan;

use std::path::Path;

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

/// The modules of `funk-ir` whose code sees every op alike, with their
/// text (`g0_scan::sources`).
fn generic_sources() -> Vec<(String, String)> {
    g0_scan::sources::generic_sources(Path::new(env!("CARGO_MANIFEST_DIR")))
}

/// Whether the code names the `dialects` module: as a part of a path, as
/// in `crate::dialects::core` or `use crate::{dialects, ir}`, or in its
/// declaration. A field, a variable or a parameter of that name is not the
/// module.
fn names_the_dialects_module(ts: &[Tok]) -> bool {
    let colons =
        |k: usize| ts.get(k) == Some(&Tok::Punct(':')) && ts.get(k + 1) == Some(&Tok::Punct(':'));
    let mut in_use = false;
    for (k, t) in ts.iter().enumerate() {
        match t {
            Tok::Ident(kw) if kw == "use" => in_use = ts.get(k + 1) != Some(&Tok::Punct('<')),
            Tok::Punct(';') => in_use = false,
            Tok::Ident(name) if name == "dialects" => {
                let after_mod = k > 0 && ts[k - 1] == Tok::Ident("mod".into());
                if in_use || after_mod || colons(k + 1) || (k >= 2 && colons(k - 2)) {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

/// Each `enum` of the code with two or more variants named after core
/// ops: a closed set of ops. One such variant is not one: the spec's own
/// `Exit` has a variant `ret`.
fn enums_of_core_ops(ts: &[Tok], variants: &[String]) -> Vec<String> {
    enum_variants(ts)
        .into_iter()
        .filter_map(|(name, vs)| {
            let ops: Vec<&String> = vs.iter().filter(|v| variants.contains(v)).collect();
            (ops.len() >= 2).then(|| format!("{name} {{ {ops:?} }}"))
        })
        .collect()
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
        if names_the_dialects_module(&code(&tokens(&src))) {
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
fn the_dialects_module_is_named_only_as_a_path() {
    let names = |src: &str| names_the_dialects_module(&code(&tokens(src)));
    for src in [
        "use crate::dialects;",
        "use crate::dialects::core::dialect;",
        "use crate::{dialects, ir};",
        "fn f() { super::dialects::core::dialect(); }",
        "fn f() { dialects::core::dialect(); }",
        "pub mod dialects;",
    ] {
        assert!(names(src), "{src}");
    }
    for src in [
        "pub fn count(dialects: &[String]) -> usize { dialects.len() }",
        "fn f(&self) -> usize { self.dialects.len() }",
        "struct R { dialects: Vec<String> }",
        "fn f(d: Vec<String>) -> R { R { dialects: d } }",
        "fn f(dialects: &[u8]) -> impl Iterator + use<'_> { dialects.iter() }",
    ] {
        assert!(!names(src), "{src}");
    }
}

#[test]
fn no_enum_is_a_closed_set_of_core_ops() {
    let variants: Vec<String> = core_ops().iter().map(|w| camel(w)).collect();
    let mut found = Vec::new();
    for (path, src) in generic_sources() {
        for e in enums_of_core_ops(&code(&tokens(&src)), &variants) {
            found.push(format!("{path}: {e}"));
        }
    }
    assert!(
        found.is_empty(),
        "a closed enum of core ops outside a dialect (ADR-2026-11-03-0600): {found:?}"
    );
    assert_eq!(camel("cond_br"), "CondBr");
    let enums = |src: &str| enums_of_core_ops(&code(&tokens(src)), &variants);
    assert_eq!(
        enums("enum OpKind { Add, Sub }"),
        ["OpKind { [\"Add\", \"Sub\"] }"]
    );
    assert_eq!(enums("enum T { Br, CondBr(u8), Ret { n: u8 } }").len(), 1);
    assert!(enums("enum Exit { Ret, Jump }").is_empty());
    assert!(enums("enum Tok { Str(String), Ident(String), Punct(char) }").is_empty());
}
