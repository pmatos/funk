//! The rules of a module's dialect set (ADR-2026-11-10-1306): the part of
//! `Module.Valid` about the set, in `lean/Fir/Validation/Rules.lean`, and
//! `Module.InDialectSet`, in `lean/Fir/Validation/DialectSet.lean`.
//!
//! The set names each dialect once, by a word, and names only registered
//! dialects other than the core, which every module holds. Every word that
//! the module writes names the core or a dialect of its set: each op's name
//! and the words of its attributes, and the words of each type that a
//! function states, at any depth. A function that writes a word of another
//! dialect gets one diagnostic, which names the first such dialect in the
//! spec's order: the function's result types, its parameters' types, the
//! types that each block defines, then each op's name and attributes.

use std::collections::HashSet;

use super::Diagnostic;
use super::func::all_blocks;
use crate::ir::names::{is_word, word_dialect};
use crate::ir::{Attr, Func, Module, Type};
use crate::registry::Registry;
use crate::text::quote;

/// The rules of the set itself, which are `Module.Valid`'s: each name is a
/// word, named once.
pub(super) fn check_names(m: &Module, out: &mut Vec<Diagnostic>) {
    for x in m.dialects.iter().filter(|x| !is_word(x)) {
        out.push(Diagnostic::module(format!(
            "the dialect set names {}, which is not a word",
            quote(x)
        )));
    }
    let mut seen = HashSet::new();
    for x in &m.dialects {
        if !seen.insert(x.as_str()) {
            out.push(Diagnostic::module(format!(
                "the dialect set names {x} more than once"
            )));
        }
    }
}

/// The rule of the set over the module's words, `Module.InDialectSet`.
pub(super) fn check_words(m: &Module, reg: &Registry, out: &mut Vec<Diagnostic>) {
    for x in m.dialects.iter().filter(|x| !reg.is_extension(x)) {
        out.push(Diagnostic::module(format!(
            "the dialect set names {x}, which is not a known dialect"
        )));
    }
    for f in m.funcs() {
        if let Some(x) = first_outside(f, &m.dialects) {
            out.push(Diagnostic::at_block(
                &f.name,
                None,
                format!(
                    "the function writes a word of the dialect {x}, which the module's dialect set does not name"
                ),
            ));
        }
    }
}

/// The first dialect, outside `declared`, that a word of `f` names.
fn first_outside<'f>(f: &'f Func, declared: &[String]) -> Option<&'f str> {
    let outside = |w: &'f str| word_dialect(w).filter(|x| !declared.iter().any(|d| d == x));
    let blocks = all_blocks(&f.body);
    let types = f
        .results
        .iter()
        .chain(f.params.iter().map(|p| &p.ty))
        .chain(blocks.iter().flat_map(|b| {
            b.params
                .iter()
                .chain(b.ops.iter().flat_map(|o| &o.results))
                .map(|d| &d.ty)
        }));
    for ty in types {
        if let Some(x) = in_type(ty, &outside) {
            return Some(x);
        }
    }
    blocks
        .iter()
        .flat_map(|b| &b.ops)
        .find_map(|o| outside(&o.name).or_else(|| in_attrs(&o.attrs, &outside)))
}

/// The first dialect that `outside` gives for a word of the type `ty`.
fn in_type<'a>(ty: &'a Type, outside: &impl Fn(&'a str) -> Option<&'a str>) -> Option<&'a str> {
    outside(&ty.name).or_else(|| ty.args.as_deref().and_then(|args| in_attrs(args, outside)))
}

/// The first dialect that `outside` gives for a word of `attrs`, in the
/// order the text writes them. Attributes nest to any depth, so the ones
/// still to look at wait on a stack (ADR-2026-10-30-1333).
fn in_attrs<'a>(
    attrs: &'a [Attr],
    outside: &impl Fn(&'a str) -> Option<&'a str>,
) -> Option<&'a str> {
    let mut pending: Vec<&'a Attr> = attrs.iter().rev().collect();
    while let Some(a) = pending.pop() {
        match a {
            Attr::Word(w) => {
                if let Some(x) = outside(w) {
                    return Some(x);
                }
            }
            Attr::App(head, args) => {
                if let Some(x) = outside(head) {
                    return Some(x);
                }
                pending.extend(args.iter().rev());
            }
            Attr::Int(_) | Attr::Str(_) | Attr::Sym(_) => {}
        }
    }
    None
}
