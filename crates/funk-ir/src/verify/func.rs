//! The rules of a function (`Func.Valid` in `lean/Fir/Validation/Rules.lean`).
//!
//! A function is valid when its entry block declares no arguments of its
//! own, every block is reachable from the entry (ADR-2026-10-30-0817), its
//! labels and value names are unique, every name and label is one or more
//! name characters, every type it states is valid, every block holds an op,
//! and every op is valid. Names and labels are checked at any depth, in the
//! blocks of ops' regions too.

use std::collections::{HashMap, HashSet};

use super::Diagnostic;
use super::cfg::Cfg;
use super::ops;
use crate::ir::names::is_name;
use crate::ir::{Block, Func, LocRef, SymbolTable, Type};
use crate::registry::{Registry, TypeCheck};

/// What a function is checked against: its module's symbols and location
/// references, and the registry.
pub(super) struct Context<'a> {
    pub symbols: &'a SymbolTable<'a>,
    pub locs: &'a HashSet<LocRef>,
    pub reg: &'a Registry,
}

/// Where a value is defined: a parameter, an argument of a block, or a
/// result of the op at an index of a block (`DefSite`).
#[derive(Clone, Copy, Debug)]
pub(super) enum Site<'f> {
    Param,
    Arg(&'f str),
    Result(&'f str, usize),
}

/// A function and what the rules of its ops look up in it.
pub(super) struct Scope<'f> {
    pub func: &'f Func,
    pub cfg: Cfg<'f>,
    /// The type of each value: its first definition, at any depth (`typeOf`).
    pub types: HashMap<&'f str, &'f Type>,
    /// Where each value is defined among the top-level blocks (`Defines`).
    pub sites: HashMap<&'f str, Vec<Site<'f>>>,
}

/// Every block of a function, at any depth, in the spec's order
/// (`Func.allBlocks`): each block, then the blocks of its ops' regions.
pub(super) fn all_blocks(blocks: &[Block]) -> Vec<&Block> {
    let mut out = Vec::new();
    let mut stack: Vec<&Block> = blocks.iter().rev().collect();
    while let Some(b) = stack.pop() {
        out.push(b);
        let inner = b
            .ops
            .iter()
            .flat_map(|o| &o.regions)
            .flat_map(|r| &r.blocks);
        let inner: Vec<&Block> = inner.collect();
        stack.extend(inner.into_iter().rev());
    }
    out
}

/// A diagnostic about a function, or about one of its blocks.
fn at(f: &Func, block: Option<&Block>, message: String) -> Diagnostic {
    Diagnostic {
        message,
        func: Some(f.name.clone()),
        block: block.map(|b| b.label.clone()),
        op: None,
        loc: block.and_then(|b| b.ops.first()).map(|o| o.loc),
    }
}

pub(super) fn check(f: &Func, cx: &Context<'_>, out: &mut Vec<Diagnostic>) {
    let blocks = &f.body.blocks;
    match blocks.first() {
        None => out.push(at(f, None, "the function has no entry block".into())),
        Some(e) if !e.params.is_empty() => out.push(at(
            f,
            Some(e),
            format!("the entry block ^{} declares arguments: its arguments are the function's parameters", e.label),
        )),
        Some(_) => {}
    }
    let all = all_blocks(blocks);
    let defs = f.params.iter().chain(
        all.iter()
            .flat_map(|b| b.params.iter().chain(b.ops.iter().flat_map(|o| &o.results))),
    );
    let mut types = HashMap::new();
    for d in defs {
        if types.contains_key(d.name.as_str()) {
            out.push(at(
                f,
                None,
                format!("value %{} is defined more than once", d.name),
            ));
        } else {
            types.insert(d.name.as_str(), &d.ty);
        }
        if !is_name(&d.name) {
            out.push(at(
                f,
                None,
                format!("value name {:?} is not one or more name characters", d.name),
            ));
        }
        check_type(f, cx.reg, &d.ty, &format!("the type of %{}", d.name), out);
    }
    for t in &f.results {
        check_type(f, cx.reg, t, "a result type of the function", out);
    }
    for b in &all {
        if !is_name(&b.label) {
            out.push(at(
                f,
                Some(b),
                format!("label {:?} is not one or more name characters", b.label),
            ));
        }
    }
    let mut labels = HashSet::new();
    let cfg = Cfg::new(f);
    for b in blocks {
        if !labels.insert(b.label.as_str()) {
            out.push(at(
                f,
                Some(b),
                format!("label ^{} names more than one block", b.label),
            ));
        }
        if !cfg.reachable(&b.label) {
            out.push(at(
                f,
                Some(b),
                format!("block ^{} is not reachable from the entry", b.label),
            ));
        }
        if b.ops.is_empty() {
            out.push(at(f, Some(b), format!("block ^{} holds no ops", b.label)));
        }
    }
    let scope = Scope {
        func: f,
        cfg,
        types,
        sites: sites(f),
    };
    for b in blocks {
        for (i, op) in b.ops.iter().enumerate() {
            ops::check(&scope, cx, b, i, op, out);
        }
    }
}

fn check_type(f: &Func, reg: &Registry, t: &Type, what: &str, out: &mut Vec<Diagnostic>) {
    match reg.check_type(t) {
        TypeCheck::Valid => {}
        TypeCheck::Invalid(why) => {
            out.push(at(f, None, format!("{what}, {t}, is not valid: {why}")))
        }
        TypeCheck::Malformed(why) => {
            out.push(at(f, None, format!("{what}, {t}, does not decode: {why}")));
        }
    }
}

/// The definition sites of each value among the top-level blocks.
fn sites(f: &Func) -> HashMap<&str, Vec<Site<'_>>> {
    let mut sites: HashMap<&str, Vec<Site<'_>>> = HashMap::new();
    for d in &f.params {
        sites.entry(d.name.as_str()).or_default().push(Site::Param);
    }
    for b in &f.body.blocks {
        for d in &b.params {
            sites
                .entry(d.name.as_str())
                .or_default()
                .push(Site::Arg(&b.label));
        }
        for (j, op) in b.ops.iter().enumerate() {
            for d in &op.results {
                sites
                    .entry(d.name.as_str())
                    .or_default()
                    .push(Site::Result(&b.label, j));
            }
        }
    }
    sites
}
