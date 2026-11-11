//! The rules of a module's dialect sets (ADR-2026-11-10-1306): the part of
//! `SymbolTable.Valid` about the set, in `lean/Fir/Validation/Rules.lean`,
//! and `SymbolTable.InDialectSet`, in `lean/Fir/Validation/DialectSet.lean`.
//! Each symbol table, the module's own and each nested module's, keeps to
//! its own set (ADR-2026-11-10-1510).
//!
//! The set names each dialect once, by a word, and names only registered
//! dialects other than the core, which every module holds. Every word that
//! the module writes names the core or a dialect of its set: each op's name,
//! the words of its attributes and the kinds of its regions, and the words
//! of each type that a function states, at any depth. A function that
//! writes a word of another dialect gets one diagnostic, which names the
//! first such dialect in the spec's order: the function's result types, its
//! parameters' types, the types that each block defines, then each op's
//! name, attributes and region kinds. An item of a dialect's kind writes
//! the words of its kind, of its types and of its attributes
//! (ADR-2026-11-10-2224), and gets one diagnostic in the same way, in the
//! order of `DialectItem.wordDialects`.

use std::collections::HashSet;

use super::Diagnostic;
use crate::ir::names::{is_word, word_dialect};
use crate::ir::tree::{Step, walk};
use crate::ir::{Attr, DialectItem, Func, Part, Table, Type};
use crate::registry::Registry;
use crate::text::quote;

/// The rules of a table's set itself, which are `SymbolTable.Valid`'s: each
/// name is a word, named once.
pub(super) fn check_names(dialects: &[String], out: &mut Vec<Diagnostic>) {
    for x in dialects.iter().filter(|x| !is_word(x)) {
        out.push(Diagnostic::module(format!(
            "the dialect set names {}, which is not a word",
            quote(x)
        )));
    }
    let mut seen = HashSet::new();
    for x in dialects {
        if !seen.insert(x.as_str()) {
            out.push(Diagnostic::module(format!(
                "the dialect set names {x} more than once"
            )));
        }
    }
}

/// The rule of a table's set over the table's words,
/// `SymbolTable.InDialectSet`.
pub(super) fn check_words(t: Table<'_>, reg: &Registry, out: &mut Vec<Diagnostic>) {
    for x in t.dialects.iter().filter(|x| !reg.is_extension(x)) {
        out.push(Diagnostic::module(format!(
            "the dialect set names {x}, which is not a known dialect"
        )));
    }
    for f in t.funcs() {
        if let Some(x) = first_outside(f, t.dialects) {
            out.push(Diagnostic::at_block(
                &f.name,
                None,
                format!(
                    "the function writes a word of the dialect {x}, which the module's dialect set does not name"
                ),
            ));
        }
    }
    for i in t.dialect_items() {
        if let Some(x) = item_outside(i, t.dialects) {
            out.push(Diagnostic::at_block(
                &i.name,
                None,
                format!(
                    "the item writes a word of the dialect {x}, which the module's dialect set does not name"
                ),
            ));
        }
    }
}

/// The first dialect, outside `declared`, that a word of the item `i`
/// names: its kind's, then those of its types, then those of its
/// attributes.
fn item_outside<'i>(i: &'i DialectItem, declared: &[String]) -> Option<&'i str> {
    let outside = |w: &'i str| word_dialect(w).filter(|x| !declared.iter().any(|d| d == x));
    outside(&i.kind)
        .or_else(|| in_types(i.types(), &outside))
        .or_else(|| in_attrs(&i.attrs, &outside))
}

/// The first dialect, outside `declared`, that a word of `f` names. Every
/// type comes before every op in the spec's order, so one walk of the
/// blocks returns at the first type outside, and otherwise gives the first
/// op word outside that it met.
fn first_outside<'f>(f: &'f Func, declared: &[String]) -> Option<&'f str> {
    let outside = |w: &'f str| word_dialect(w).filter(|x| !declared.iter().any(|d| d == x));
    if let Some(x) = in_types(
        f.results.iter().chain(f.params.iter().map(|p| &p.ty)),
        &outside,
    ) {
        return Some(x);
    }
    let mut first_op = None;
    for part in f.body.parts() {
        let Part::Block(b) = part else { continue };
        let defs = b.params.iter().chain(b.ops.iter().flat_map(|o| &o.results));
        if let Some(x) = in_types(defs.map(|d| &d.ty), &outside) {
            return Some(x);
        }
        if first_op.is_none() {
            first_op = b.ops.iter().find_map(|o| {
                outside(&o.name)
                    .or_else(|| in_attrs(&o.attrs, &outside))
                    .or_else(|| {
                        o.regions
                            .iter()
                            .find_map(|r| r.kind.as_deref().and_then(outside))
                    })
            });
        }
    }
    first_op
}

/// The first dialect that `outside` gives for a word of the types `tys`.
fn in_types<'a>(
    mut tys: impl Iterator<Item = &'a Type>,
    outside: &impl Fn(&'a str) -> Option<&'a str>,
) -> Option<&'a str> {
    tys.find_map(|t| in_type(t, outside))
}

/// The first dialect that `outside` gives for a word of the type `ty`.
fn in_type<'a>(ty: &'a Type, outside: &impl Fn(&'a str) -> Option<&'a str>) -> Option<&'a str> {
    outside(&ty.name).or_else(|| ty.args.as_deref().and_then(|args| in_attrs(args, outside)))
}

/// The first dialect that `outside` gives for a word of `attrs`, in the
/// order the text writes them, at any depth.
fn in_attrs<'a>(
    attrs: &'a [Attr],
    outside: &impl Fn(&'a str) -> Option<&'a str>,
) -> Option<&'a str> {
    attrs.iter().find_map(|a| {
        walk(a).filter_map(Step::entered).find_map(|n| match n {
            Attr::Word(w) | Attr::App(w, _) => outside(w),
            Attr::Int(_) | Attr::Str(_) | Attr::Sym(_) => None,
        })
    })
}
