//! Integer arithmetic: `add`, `sub` and `mul` with their flags
//! (`dialects/core/arith.rs` in `funk-ir`).
//!
//! Each op wraps modulo `2^N`. The low `N` bits of a 64-bit sum, difference
//! or product depend only on the low `N` bits of the operands, so one 64-bit
//! `addq`, `subq` or `imulq` computes the op at every width up to 64,
//! whatever the bits above `N` hold
//! (`docs/decisions/x86-64-backend.md#values-and-widths`).
//!
//! At `i128` the halves are in `%rax` and `%rdx`
//! (`docs/decisions/x86-64-backend-lowering.md#lowering-i128`). `add` is
//! `addq` of the low halves and `adcq` of the high ones, which adds the
//! carry, and `sub` is `subq` and `sbbq`, which subtracts the borrow. `mul`
//! keeps the low 128 bits of the product: `mulq` gives the whole 128-bit
//! product of the low halves, and the two cross products, each the low 64
//! bits of one low half times the other high half, add into its high half.
//! The product of the high halves is a multiple of `2^128`.
//!
//! A broken `nuw` or `nsw` gives poison, which any value of the type
//! refines (ADR-2026-10-29-2008), so a flagged op is lowered as the op
//! without flags: its result is then the wrapped one (ADR-2026-10-30-2248).

use funk_ir::Op;

use super::{Cx, Lower, Unlowered, is_pair};
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
    if is_pair(cx, op)? {
        return halves(cx, op, "addq", "adcq");
    }
    binary(cx, op, "addq")
}

/// `%d: iN = sub %a, %b`: `%a` minus `%b`.
fn sub(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    if is_pair(cx, op)? {
        return halves(cx, op, "subq", "sbbq");
    }
    binary(cx, op, "subq")
}

/// `%p: iN = mul %a, %b`. The low 64 bits of a product are the same read
/// as signed or as unsigned, so the signed `imulq` serves both.
fn mul(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    if !is_pair(cx, op)? {
        return binary(cx, op, "imulq");
    }
    let ([a, b], [r]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err("mul takes two operands and defines one value".into());
    };
    let (sa, sb) = (cx.slot(a)?, cx.slot(b)?);
    let (rax, rcx) = (Reg::Rax.q(), Reg::Rcx.q());
    cx.asm.ins("movq", format_args!("{sa}, {rax}"));
    cx.asm.ins("mulq", format_args!("{sb}"));
    cx.asm.ins("movq", format_args!("{sa}, {rcx}"));
    cx.asm.ins("imulq", format_args!("{}, {rcx}", sb.high()));
    cx.asm.ins("addq", format_args!("{rcx}, %rdx"));
    cx.asm.ins("movq", format_args!("{}, {rcx}", sa.high()));
    cx.asm.ins("imulq", format_args!("{sb}, {rcx}"));
    cx.asm.ins("addq", format_args!("{rcx}, %rdx"));
    cx.store_pair(&r.name, Reg::Rax, Reg::Rdx)
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

/// [`binary`] at `i128`: loads `%a` into `%rax` and `%rdx`, applies `low`
/// to the low halves and then `high` to the high ones, with `%b`'s slots
/// as their sources, and stores the pair as the result. `high` comes right
/// after `low`, so that `adcq` and `sbbq` read the carry or borrow that
/// `addq` and `subq` leave.
pub(super) fn halves(cx: &mut Cx<'_>, op: &Op, low: &str, high: &str) -> Result<(), Unlowered> {
    let ([a, b], [r]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err(format!("{} takes two operands and defines one value", op.name).into());
    };
    cx.load_pair(Reg::Rax, Reg::Rdx, a)?;
    let b = cx.slot(b)?;
    cx.asm.ins(low, format_args!("{b}, {}", Reg::Rax.q()));
    cx.asm
        .ins(high, format_args!("{}, {}", b.high(), Reg::Rdx.q()));
    cx.store_pair(&r.name, Reg::Rax, Reg::Rdx)
}
