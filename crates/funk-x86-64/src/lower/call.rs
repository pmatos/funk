//! Calls: `call` (`dialects/core/call.rs` in `funk-ir`).
//!
//! Width checks and result storage live here. [`crate::abi::call`] owns
//! outgoing argument placement, symbol spelling and stack cleanup
//! (ADR-2026-11-02-1428). Arguments and results move as their slots hold
//! them, without extension (ADR-2026-11-02-1021). Every value lives in its
//! slot, so nothing needs saving around the call. A call has any number of
//! results, which [`crate::abi::results`] lays out (ADR-2026-11-03-0109):
//! when they go in memory, the call passes the address of its frame's
//! result area first, and copies each result out of the area after it. An
//! `i128` passes as two eightbytes (ADR-2026-11-03-0108), and comes back in
//! two: alone in `%rdx:%rax`, and among other results in the area.

use funk_ir::{Attr, Op};

use super::{Cx, Lower, Unlowered};
use crate::abi::{self, Arg, results::Layout};
use crate::width::PAIR;

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
    let mut args = Vec::with_capacity(op.operands.len() + 1);
    for x in &op.operands {
        let words = if cx.width(x)? == PAIR { 2 } else { 1 };
        args.push(Arg {
            slot: cx.slot(x)?,
            words,
        });
    }
    let mut widths = Vec::with_capacity(op.results.len());
    let mut into = Vec::with_capacity(op.results.len());
    for d in &op.results {
        widths.push(cx.width(&d.name)?);
        into.extend(cx.eightbytes(&d.name)?);
    }
    let layout = Layout::new(&widths)?;
    let area = if layout.in_memory() {
        let area = cx.frame.result_area();
        Some(area.ok_or("the frame has no result area for the call")?)
    } else {
        None
    };
    // The area's address is the call's first argument, of one eightbyte.
    if let Some(area) = area {
        args.insert(
            0,
            Arg {
                slot: area.address,
                words: 1,
            },
        );
        layout.pass(&mut cx.asm, area);
    }
    abi::call(&mut cx.asm, callee, &args)?;
    layout.receive(&mut cx.asm, area, &into)?;
    Ok(())
}
