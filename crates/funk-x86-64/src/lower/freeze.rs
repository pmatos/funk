//! Poison control: `freeze` (`dialects/core/freeze.rs` in `funk-ir`).
//!
//! Native code holds no poison: every value is the bits in its slot, and an
//! op whose result would be poison writes some bits there all the same. So
//! `freeze` copies its operand's bits into its own slot, which no other op
//! writes. Every use of the result loads that one slot, so every use sees
//! the same bits (ADR-2026-10-29-2006, ADR-2026-10-30-2248).

use funk_ir::Op;

use super::{Cx, Lower, Unlowered};
use crate::asm::Reg;

pub(super) fn lowering(name: &str) -> Option<Lower> {
    match name {
        "freeze" => Some(freeze),
        _ => None,
    }
}

/// `%f: iN = freeze %x`.
fn freeze(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    let ([x], [f]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err("freeze takes one operand and defines one value".into());
    };
    cx.width(&f.name)?;
    cx.load(Reg::Rax, x)?;
    cx.store(&f.name, Reg::Rax)
}
