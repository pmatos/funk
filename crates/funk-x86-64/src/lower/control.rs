//! Control flow: `ret` (`dialects/core/control.rs` in `funk-ir`).
//!
//! `ret` puts its value, if it has one, in the result register, then
//! returns (ADR-2026-10-30-1232). An `i1` result is returned as 0 or 1 in the whole
//! register, as C's `_Bool` is. A function with more than one result needs
//! a convention for the others, which #31 decides; until then the backend
//! reports it at the `ret`.

use funk_ir::Op;

use super::{Cx, Lower, Unlowered};
use crate::abi::RESULT_REG;
use crate::frame;
use crate::width::{self, Ext};

pub(super) fn lowering(name: &str) -> Option<Lower> {
    match name {
        "ret" => Some(ret),
        _ => None,
    }
}

/// `ret %a`, or `ret` with no value.
fn ret(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    match op.operands.as_slice() {
        [] => {}
        [v] => {
            let w = cx.width(v)?;
            cx.load(RESULT_REG, v)?;
            if w == 1 {
                width::extend(&mut cx.asm, Ext::Zero, 1, RESULT_REG);
            }
        }
        vs => {
            return Err(format!(
                "ret returns {} values: the x86-64 backend returns at most one value \
                 so far",
                vs.len()
            )
            .into());
        }
    }
    frame::epilogue(&mut cx.asm);
    Ok(())
}
