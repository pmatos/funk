//! The rules of an item of a dialect's kind (`DialectItem.Valid` in
//! `lean/Fir/Validation/Rules.lean`, ADR-2026-11-10-2224), in the order of
//! `DialectItem.problems`: its kind is a word of a dialect, its parameters
//! are named by distinct names, its types are valid, its attributes can be
//! written, and a dialect registers its kind and the item obeys that
//! kind's rule. A kind that no dialect registers has no rule to break.

use std::collections::HashSet;

use super::Diagnostic;
use crate::ir::names::{is_dialect_word, is_name, is_word};
use crate::ir::tree::{Step, walk};
use crate::ir::{Attr, DialectItem, SymbolTable};
use crate::registry::{FuncContext, Registry, TypeCheck};
use crate::text::quote;

/// Checks the item `i` of a dialect's kind, with the symbols of its table.
pub(super) fn check(
    i: &DialectItem,
    symbols: &SymbolTable<'_>,
    reg: &Registry,
    out: &mut Vec<Diagnostic>,
) {
    let at = |message: String| Diagnostic::at_block(&i.name, None, message);
    if !is_dialect_word(&i.kind) {
        out.push(at(format!(
            "the kind {} is not a word of a dialect",
            quote(&i.kind)
        )));
    }
    for p in i.params.iter().filter(|p| !is_name(&p.name)) {
        out.push(at(format!(
            "the parameter %{} is not a name",
            quote(&p.name)
        )));
    }
    let mut seen = HashSet::new();
    for p in &i.params {
        if !seen.insert(p.name.as_str()) {
            out.push(at(format!("the item defines %{} more than once", p.name)));
        }
    }
    if i.types().any(|t| reg.check_type(t) != TypeCheck::Valid) {
        out.push(at("a type of the item is not valid".to_string()));
    }
    if !i.attrs.iter().all(writable) {
        out.push(at("an attribute of the item cannot be written".to_string()));
    }
    match reg.item_kind(&i.kind) {
        Some(spec) => {
            if let Err(why) = spec.check(&FuncContext { symbols }, i) {
                out.push(at(format!(
                    "the item breaks the rule of its kind {}: {why}",
                    quote(&i.kind)
                )));
            }
        }
        None => out.push(at(format!(
            "no dialect registers the kind of item {}",
            quote(&i.kind)
        ))),
    }
}

/// Whether the text can write an attribute (`Attr.Writable`): each word, and
/// each word that it applies, is a word, at any depth.
fn writable(a: &Attr) -> bool {
    walk(a).filter_map(Step::entered).all(|n| match n {
        Attr::Word(w) | Attr::App(w, _) => is_word(w),
        Attr::Int(_) | Attr::Str(_) | Attr::Sym(_) => true,
    })
}
