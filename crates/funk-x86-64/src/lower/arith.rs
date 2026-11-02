//! Integer arithmetic: `add`, `sub` and `mul` with their flags
//! (`dialects/core/arith.rs` in `funk-ir`).
//!
//! Each op wraps modulo `2^N`. The low `N` bits of a 64-bit sum, difference
//! or product depend only on the low `N` bits of the operands, so one 64-bit
//! `addq`, `subq` or `imulq` computes the op at every width, whatever the
//! bits above `N` hold (ADR-2026-10-30-1231).
//!
//! A broken `nuw` or `nsw` gives poison, which any value of the type
//! refines (ADR-2026-10-29-2008), so a flagged op is lowered as the op
//! without flags: its result is then the wrapped one (ADR-2026-10-30-2248).

use funk_ir::Op;

use super::{Cx, Lower, Unlowered};
use crate::asm::Reg;

pub(super) fn lowering(name: &str) -> Option<Lower> {
    match name {
        "add" => Some(add),
        "sub" => Some(sub),
        "mul" => Some(mul),
        _ => None,
    }
}

/// `%s: iN = add %a, %b`.
fn add(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    binary(cx, op, "addq")
}

/// `%d: iN = sub %a, %b`: `%a` minus `%b`.
fn sub(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    binary(cx, op, "subq")
}

/// `%p: iN = mul %a, %b`. The low 64 bits of a product are the same read
/// as signed or as unsigned, so the signed `imulq` serves both.
fn mul(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    binary(cx, op, "imulq")
}

/// Loads `%a` into `%rax`, applies `mnemonic` with `%b`'s slot as its
/// source, and stores `%rax` as the result.
pub(super) fn binary(cx: &mut Cx<'_>, op: &Op, mnemonic: &str) -> Result<(), Unlowered> {
    let ([a, b], [r]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err(format!("{} takes two operands and defines one value", op.name).into());
    };
    cx.width(&r.name)?;
    cx.load(Reg::Rax, a)?;
    let b = cx.slot(b)?;
    cx.asm.ins(mnemonic, format_args!("{b}, {}", Reg::Rax.q()));
    cx.store(&r.name, Reg::Rax)
}
