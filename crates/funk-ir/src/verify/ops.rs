//! The rules of an op (`Func.OpValid` in `lean/Fir/Validation/Rules.lean`).
//!
//! An op at index `i` of block `b` is valid when it owns no region; it is
//! registered, and its attributes, operand types and result types decode
//! through its registration; it is a terminator exactly when it is the last
//! op of its block, with as many successors as its registration says and
//! none if it is not a terminator; each successor is valid; each value it
//! uses is in scope; each symbol it refers to names a function; its
//! dialect's own rule holds; and its location reference is a key of the
//! location table.

use super::Diagnostic;
use super::func::{Context, Scope, Site};
use crate::ir::{Block, Item, Op, Succ, Type};
use crate::registry::{OpContext, OpShape, OpTypes};
use crate::text::Commas;

struct At<'a> {
    func: &'a str,
    block: &'a Block,
    index: usize,
    op: &'a Op,
}

impl At<'_> {
    fn diag(&self, message: String) -> Diagnostic {
        Diagnostic {
            message,
            func: Some(self.func.to_string()),
            block: Some(self.block.label.clone()),
            op: Some(self.index),
            loc: Some(self.op.loc),
        }
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
    if !op.regions.is_empty() {
        out.push(at.diag(format!(
            "op {} owns a region: no op may own one yet",
            op.name
        )));
    }
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
    check_shape(&at, &shape, out);
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
}

fn check_shape(at: &At<'_>, shape: &OpShape, out: &mut Vec<Diagnostic>) {
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
    if !shape.terminator && !op.succs.is_empty() {
        out.push(at.diag(format!(
            "{} is not a terminator, and only terminators have successors",
            op.name
        )));
    } else if op.succs.len() != shape.successors {
        out.push(at.diag(format!(
            "{} has {} successors, and its registration says {}",
            op.name,
            op.succs.len(),
            shape.successors
        )));
    }
}

/// A successor names a block other than the entry, and passes one value of
/// the right type for each of that block's arguments (`SuccValid`).
fn check_succ(s: &Scope<'_>, at: &At<'_>, su: &Succ, out: &mut Vec<Diagnostic>) {
    let blocks = &s.func.body.blocks;
    if blocks.first().is_some_and(|e| e.label == su.label) {
        out.push(at.diag(format!("no branch may go to the entry block ^{}", su.label)));
    }
    let Some(target) = s.blocks.get(su.label.as_str()) else {
        out.push(at.diag(format!(
            "successor ^{} is not a block of the function",
            su.label
        )));
        return;
    };
    for a in &su.args {
        if !s.types.contains_key(a.as_str()) {
            out.push(at.diag(format!(
                "successor argument %{a} is not defined in the function"
            )));
        }
    }
    let passed: Vec<&Type> = su
        .args
        .iter()
        .filter_map(|a| s.types.get(a.as_str()).copied())
        .collect();
    let wanted: Vec<&Type> = target.params.iter().map(|d| &d.ty).collect();
    if passed.len() == su.args.len() && passed != wanted {
        out.push(at.diag(format!(
            "successor ^{} passes ({}) but the block takes ({})",
            su.label,
            Commas(&passed),
            Commas(&wanted)
        )));
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
