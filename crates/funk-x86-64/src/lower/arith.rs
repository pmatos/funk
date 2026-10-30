//! Integer arithmetic: `add` (`dialects/core/arith.rs` in `funk-ir`).
//!
//! `add` wraps modulo `2^N`. The low `N` bits of a 64-bit sum depend only on
//! the low `N` bits of the operands, so one 64-bit `addq` adds at every
//! width, whatever the bits above `N` hold (ADR-2026-10-30-1231).

use funk_ir::Op;

use super::{Cx, Lower, Unlowered};
use crate::asm::Reg;

pub(super) fn lowering(name: &str) -> Option<Lower> {
    match name {
        "add" => Some(add),
        _ => None,
    }
}

/// `%s: iN = add %a, %b`.
fn add(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    if !op.attrs.is_empty() {
        return Err("the x86-64 backend lowers add without flags only".into());
    }
    let ([a, b], [s]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err("add takes two operands and defines one value".into());
    };
    cx.width(&s.name)?;
    cx.load(Reg::Rax, a)?;
    let b = cx.slot(b)?;
    cx.asm.ins("addq", format_args!("{b}, {}", Reg::Rax.q()));
    cx.store(&s.name, Reg::Rax)
}
