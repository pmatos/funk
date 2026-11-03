//! Calls: `call` (`dialects/core/call.rs` in `funk-ir`).
//!
//! Width checks and result storage live here. [`crate::abi::call`] owns
//! outgoing argument placement, symbol spelling and stack cleanup
//! (ADR-2026-11-02-1428). Arguments and results move as their slots hold
//! them, without extension (ADR-2026-11-02-1021). Every value lives in its
//! slot, so nothing needs saving around the call. More than one result
//! needs the convention of #31 and is reported at the call until then. An
//! `i128` passes as two eightbytes, and comes back in `%rdx:%rax`
//! (ADR-2026-11-03-0108).

use funk_ir::{Attr, Op};

use super::{Cx, Lower, Unlowered};
use crate::abi::{self, Arg, RESULT_HIGH_REG, RESULT_REG};
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

/// `%r = call @f %a, %b`.
fn call(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    let Some(callee) = callee(op) else {
        return Err("call names its callee by one symbol".into());
    };
    if op.results.len() > 1 {
        return Err(format!(
            "call returns {} values: the x86-64 backend returns at most one value so far",
            op.results.len()
        )
        .into());
    }
    let mut args = Vec::with_capacity(op.operands.len());
    for x in &op.operands {
        let words = if cx.width(x)? == PAIR { 2 } else { 1 };
        args.push(Arg {
            slot: cx.slot(x)?,
            words,
        });
    }
    for d in &op.results {
        cx.width(&d.name)?;
    }
    abi::call(&mut cx.asm, callee, &args)?;
    if let [r] = op.results.as_slice() {
        if cx.width(&r.name)? == PAIR {
            cx.store_pair(&r.name, RESULT_REG, RESULT_HIGH_REG)?;
        } else {
            cx.store(&r.name, RESULT_REG)?;
        }
    }
    Ok(())
}
