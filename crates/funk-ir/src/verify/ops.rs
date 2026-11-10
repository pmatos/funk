//! The rules of an op (`Func.OpValid` in `lean/Fir/Validation/Rules.lean`),
//! and of an op inside a region of an op (`Func.InnerOpValid`).
//!
//! An op at index `i` of block `b` of a function's body is valid when it is
//! registered, and its attributes, operand types and result types decode
//! through its registration; it is a terminator exactly when it is the last
//! op of its block, with as many successors as its registration says and
//! none if it is not a terminator; each successor is valid; each value it
//! uses is in scope; each symbol it refers to names a function; its
//! dialect's own rule holds; its location reference is a key of the
//! location table; and its regions have the kinds that its registration
//! states, each registered, and each obeys the rule of its kind
//! (`Func.RegionsValid`, ADR-2026-11-10-1941).
//!
//! An op inside a region of an op obeys the same rules but three, which the
//! rule of its region's kind decides: where it stands in its block, where
//! its successors go, and which values it may use. Its successors' labels
//! are still names, and the values they pass are defined in the function.

use super::Diagnostic;
use super::func::{Context, Scope, Site};
use crate::ir::names::{is_name, is_word};
use crate::ir::{Block, Item, Op, Succ, Type};
use crate::registry::{FuncContext, OpContext, OpShape, OpTypes};
use crate::text::{Commas, quote};

struct At<'a> {
    func: &'a str,
    block: &'a Block,
    index: usize,
    op: &'a Op,
}

impl At<'_> {
    fn diag(&self, message: String) -> Diagnostic {
        Diagnostic::at_op(self.func, self.block, self.index, message)
    }
}

pub(super) fn check(
    s: &Scope<'_>,
    cx: &Context<'_>,
    b: &Block,
    i: usize,
    op: &Op,
    out: &mut Vec<Diagnostic>,
) {
    let at = At {
        func: &s.func.name,
        block: b,
        index: i,
        op,
    };
    for su in &op.succs {
        check_succ(s, &at, su, out);
    }
    for x in op
        .operands
        .iter()
        .chain(op.succs.iter().flat_map(|su| &su.args))
    {
        if s.types.contains_key(x.as_str()) {
            check_scope(s, &at, x, out);
        }
    }
    check_general(s, cx, &at, true, out);
}

/// The rules of an op inside a region of an op: those that hold whatever
/// the kind of its region (`Func.InnerOpValid`).
pub(super) fn check_inner(
    s: &Scope<'_>,
    cx: &Context<'_>,
    b: &Block,
    i: usize,
    op: &Op,
    out: &mut Vec<Diagnostic>,
) {
    let at = At {
        func: &s.func.name,
        block: b,
        index: i,
        op,
    };
    for su in &op.succs {
        if !is_name(&su.label) {
            out.push(at.diag(format!(
                "successor label {} is not one or more name characters",
                quote(&su.label)
            )));
        }
        check_succ_args(s, &at, su, out);
    }
    check_general(s, cx, &at, false, out);
}

/// The rules of an op that hold in every region: its location, its
/// operand and result types through its registration, its count of
/// successors, the symbols it refers to, its dialect's own rule and its
/// regions; and, when `place`, for an op of a function's body, that it is a
/// terminator exactly when it is the last op of its block.
fn check_general(
    s: &Scope<'_>,
    cx: &Context<'_>,
    at: &At<'_>,
    place: bool,
    out: &mut Vec<Diagnostic>,
) {
    let op = at.op;
    check_region_kinds(s, cx, at, out);
    if !cx.locs.contains(&op.loc) {
        out.push(at.diag(format!(
            "location reference {} is not in the location table",
            op.loc
        )));
    }
    let mut operand_types = Vec::new();
    for x in &op.operands {
        match s.types.get(x.as_str()) {
            Some(t) => operand_types.push((*t).clone()),
            None => out.push(at.diag(format!("operand %{x} is not defined in the function"))),
        }
    }
    let Some(spec) = cx.reg.op(&op.name) else {
        out.push(at.diag(format!("op {} is not registered", op.name)));
        return;
    };
    if operand_types.len() != op.operands.len() {
        return;
    }
    let result_types: Vec<Type> = op.results.iter().map(|d| d.ty.clone()).collect();
    let types = OpTypes {
        attrs: &op.attrs,
        operands: &operand_types,
        results: &result_types,
    };
    let shape = match spec.decode(&types) {
        Ok(shape) => shape,
        Err(why) => {
            out.push(at.diag(format!(
                "op {} does not match its registration: {why}",
                op.name
            )));
            return;
        }
    };
    if place {
        check_place(at, &shape, out);
    }
    check_counts(at, &shape, out);
    for g in &shape.symbols {
        if cx.symbols.get(g).and_then(Item::as_func).is_none() {
            let sym = crate::text::print_symbol(g);
            out.push(at.diag(format!(
                "op {} refers to {sym}, which names no function",
                op.name
            )));
        }
    }
    let ocx = OpContext {
        symbols: cx.symbols,
        func: &s.func.name,
        results: &s.func.results,
    };
    if let Err(why) = spec.check(&ocx, &types) {
        out.push(at.diag(why));
    }
    if !op
        .regions
        .iter()
        .map(|r| r.kind.as_deref())
        .eq(shape.regions.iter().map(|k| Some(k.as_str())))
    {
        out.push(at.diag(format!(
            "the regions of {} are not of the kinds that its registration states",
            op.name
        )));
    }
}

/// An op of a function's body is a terminator exactly when it is the last
/// op of its block.
fn check_place(at: &At<'_>, shape: &OpShape, out: &mut Vec<Diagnostic>) {
    let (op, last) = (at.op, at.index + 1 == at.block.ops.len());
    if shape.terminator && !last {
        out.push(at.diag(format!(
            "{} ends a block, and is not the last op of ^{}",
            op.name, at.block.label
        )));
    }
    if !shape.terminator && last {
        out.push(at.diag(format!(
            "block ^{} does not end with a terminator",
            at.block.label
        )));
    }
}

/// An op has as many successors as its registration says, and none when it
/// is not a terminator.
fn check_counts(at: &At<'_>, shape: &OpShape, out: &mut Vec<Diagnostic>) {
    let op = at.op;
    if op.succs.len() != shape.successors {
        out.push(at.diag(format!(
            "{} has {} successors, and its registration says {}",
            op.name,
            op.succs.len(),
            shape.successors
        )));
    }
    if !shape.terminator && !op.succs.is_empty() {
        out.push(at.diag(format!(
            "{} is not a terminator, and only terminators have successors",
            op.name
        )));
    }
}

/// Each region of an op that names a kind names a word that a dialect
/// registers, and obeys its kind's rule (`Func.RegionsValid`). These hold
/// whether or not the op decodes; that the kinds are those its registration
/// states is checked once it does. A region of the core's kind names no
/// kind, and no registration states it.
fn check_region_kinds(s: &Scope<'_>, cx: &Context<'_>, at: &At<'_>, out: &mut Vec<Diagnostic>) {
    let op = at.op;
    let fcx = FuncContext {
        symbols: cx.symbols,
    };
    for r in &op.regions {
        let Some(k) = r.kind.as_deref() else {
            continue;
        };
        if !is_word(k) {
            out.push(at.diag(format!(
                "a region of {} is of kind {}, which is not a word",
                op.name,
                quote(k)
            )));
            continue;
        }
        match cx.reg.region_kind(k) {
            None => out.push(at.diag(format!(
                "a region of {} is of kind {k}, which no dialect registers",
                op.name
            ))),
            Some(spec) => {
                if let Err(why) = spec.check(&fcx, s.func, r) {
                    out.push(at.diag(format!(
                        "a region of {} breaks the rule of its kind {k}: {why}",
                        op.name
                    )));
                }
            }
        }
    }
}

/// A successor names a block other than the entry, and passes one value of
/// the right type for each of that block's arguments (`SuccValid`). Each
/// argument that is not defined is a use out of scope, whatever the block;
/// it has no type either, so it breaks `SuccValid` too, and the message
/// shows it by its name.
fn check_succ(s: &Scope<'_>, at: &At<'_>, su: &Succ, out: &mut Vec<Diagnostic>) {
    let blocks = &s.func.body.blocks;
    if blocks.first().is_some_and(|e| e.label == su.label) {
        out.push(at.diag(format!("no branch may go to the entry block ^{}", su.label)));
    }
    check_succ_args(s, at, su, out);
    let Some(target) = s.blocks.get(su.label.as_str()) else {
        out.push(at.diag(format!(
            "successor ^{} is not a block of the function",
            su.label
        )));
        return;
    };
    let passed: Vec<Option<&Type>> = su
        .args
        .iter()
        .map(|a| s.types.get(a.as_str()).copied())
        .collect();
    let wanted: Vec<&Type> = target.params.iter().map(|d| &d.ty).collect();
    if !passed.iter().copied().eq(wanted.iter().copied().map(Some)) {
        let shown: Vec<String> = su
            .args
            .iter()
            .zip(&passed)
            .map(|(a, &t)| t.map_or_else(|| format!("%{a}"), Type::to_string))
            .collect();
        out.push(at.diag(format!(
            "successor ^{} passes ({}) but the block takes ({})",
            su.label,
            Commas(&shown),
            Commas(&wanted)
        )));
    }
}

/// Each value that a successor passes is defined in the function.
fn check_succ_args(s: &Scope<'_>, at: &At<'_>, su: &Succ, out: &mut Vec<Diagnostic>) {
    for a in &su.args {
        if !s.types.contains_key(a.as_str()) {
            out.push(at.diag(format!(
                "successor argument %{a} is not defined in the function"
            )));
        }
    }
}

/// A use is in scope: defined among the function's top-level blocks, and
/// each definition dominates the use (`InScope`, `DominatesUse`).
fn check_scope(s: &Scope<'_>, at: &At<'_>, x: &str, out: &mut Vec<Diagnostic>) {
    let here = at.block.label.as_str();
    let Some(sites) = s.sites.get(x) else {
        out.push(at.diag(format!(
            "%{x} is defined inside a region, and is not in scope here"
        )));
        return;
    };
    for site in sites {
        let why = match *site {
            Site::Param => None,
            Site::Arg(a) if s.cfg.dominates(a, here) => None,
            Site::Arg(a) => Some(format!(
                "%{x} is an argument of ^{a}, which does not dominate ^{here}"
            )),
            Site::Result(a, j) if a == here && j < at.index => None,
            Site::Result(a, _) if a == here => Some(format!("%{x} is used before it is defined")),
            Site::Result(a, _) if s.cfg.dominates(a, here) => None,
            Site::Result(a, _) => Some(format!(
                "%{x} is defined in ^{a}, which does not dominate ^{here}"
            )),
        };
        if let Some(why) = why {
            out.push(at.diag(why));
        }
    }
}
