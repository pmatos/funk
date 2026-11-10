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
use crate::ir::names::{is_word, word_dialect};
use crate::ir::tree::{Step, walk};
use crate::ir::{Attr, Func, Module, Part, Type};
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
            first_op = b
                .ops
                .iter()
                .find_map(|o| outside(&o.name).or_else(|| in_attrs(&o.attrs, &outside)));
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
