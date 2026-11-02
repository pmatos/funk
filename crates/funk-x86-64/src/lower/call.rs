//! Calls: `call` (`dialects/core/call.rs` in `funk-ir`).
//!
//! Width checks and result storage live here. [`crate::abi::call`] owns
//! outgoing argument placement, symbol spelling and stack cleanup
//! (ADR-2026-11-02-1428). Arguments and results move as their slots hold
//! them, without extension (ADR-2026-11-02-1021). Every value lives in its
//! slot, so nothing needs saving around the call. More than one result
//! needs the convention of #31 and is reported at the call until then.

use funk_ir::{Attr, Op};

use super::{Cx, Lower, Unlowered};
use crate::abi::{self, RESULT_REG};

pub(super) fn lowering(name: &str) -> Option<Lower> {
    match name {
        "call" => Some(call),
        _ => None,
    }
}

/// `%r = call @f %a, %b`.
fn call(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    let [Attr::Sym(callee)] = op.attrs.as_slice() else {
        return Err("call names its callee by one symbol".into());
    };
    if op.results.len() > 1 {
        return Err(format!(
            "call returns {} values: the x86-64 backend returns at most one value so far",
            op.results.len()
        )
        .into());
    }
    for x in &op.operands {
        cx.width(x)?;
    }
    for d in &op.results {
        cx.width(&d.name)?;
    }
    let args = op
        .operands
        .iter()
        .map(|x| cx.slot(x))
        .collect::<Result<Vec<_>, _>>()?;
    abi::call(&mut cx.asm, callee, &args)?;
    if let [r] = op.results.as_slice() {
        cx.store(&r.name, RESULT_REG)?;
    }
    Ok(())
}
