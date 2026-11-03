//! Calls: `call` (`dialects/core/call.rs` in `funk-ir`).
//!
//! Width checks and result storage live here. [`crate::abi::call`] owns
//! outgoing argument placement, symbol spelling and stack cleanup
//! (ADR-2026-11-02-1428). Arguments and results move as their slots hold
//! them, without extension (ADR-2026-11-02-1021). Every value lives in its
//! slot, so nothing needs saving around the call. A call has any number of
//! results, which [`crate::abi::results`] lays out (ADR-2026-11-03-0109):
//! when they go in memory, the call passes the address of its frame's
//! result area first, and copies each result out of the area after it.

use funk_ir::{Attr, Op};

use super::{Cx, Lower, Unlowered};
use crate::abi::{self, results::Layout};

pub(super) fn lowering(name: &str) -> Option<Lower> {
    match name {
        "call" => Some(call),
        _ => None,
    }
}

/// The function that `op` calls, if it is a `call`.
pub fn callee(op: &Op) -> Option<&str> {
    match (op.name.as_str(), op.attrs.as_slice()) {
        ("call", [Attr::Sym(callee)]) => Some(callee),
        _ => None,
    }
}

/// `%r, %s = call @f %a, %b`.
fn call(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    let Some(callee) = callee(op) else {
        return Err("call names its callee by one symbol".into());
    };
    for x in &op.operands {
        cx.width(x)?;
    }
    let mut widths = Vec::with_capacity(op.results.len());
    for d in &op.results {
        widths.push(cx.width(&d.name)?);
    }
    let layout = Layout::new(&widths)?;
    let area = if layout.in_memory() {
        let area = cx.frame.result_area();
        Some(area.ok_or("the frame has no result area for the call")?)
    } else {
        None
    };
    let mut args = Vec::with_capacity(layout.hidden_arguments() + op.operands.len());
    args.extend(area.map(|a| a.address));
    for x in &op.operands {
        args.push(cx.slot(x)?);
    }
    let into = op
        .results
        .iter()
        .map(|r| cx.slot(&r.name))
        .collect::<Result<Vec<_>, _>>()?;
    if let Some(area) = area {
        layout.pass(&mut cx.asm, area);
    }
    abi::call(&mut cx.asm, callee, &args)?;
    layout.receive(&mut cx.asm, area, &into)?;
    Ok(())
}
