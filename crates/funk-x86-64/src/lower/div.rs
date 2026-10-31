//! Division and remainder: `sdiv`, `udiv`, `srem` and `urem`
//! (`dialects/core/div.rs` in `funk-ir`; ADR-2026-10-31-0050).
//!
//! Each op is one `idiv` (`sdiv`, `srem`) or `div` (`udiv`, `urem`) of the
//! op's own size: `b`, `w`, `l` or `q` for `i8`, `i16`, `i32` and `i64`.
//! The divisor is `%rcx` at that size, which reads only the value's bits.
//! The dividend is `%rax` at that size, widened into the high half that the
//! instruction also reads: by sign with `cbtw`, `cwtd`, `cltd` or `cqto`,
//! by zero with `movzbl %al, %eax`, which clears `%ah`, or with
//! `xorl %edx, %edx`. The quotient is in `%al`, `%ax`, `%eax` or `%rax`;
//! the remainder in `%ah`, `%dx`, `%edx` or `%rdx`. `i1` has no division
//! of its own: both operands are extended to 64 bits
//! (ADR-2026-10-30-1231) and divided as `i8`.
//!
//! No code tests the divisor. A zero divisor, and the signed minimum
//! divided by `-1`, are immediate UB in the source, so whatever `idiv` or
//! `div` does on them, a trap included, is correct. A broken `exact` gives
//! poison, which any value refines (ADR-2026-10-29-2008), so `exact`
//! lowers as the plain quotient (ADR-2026-10-30-2248).

use funk_ir::Op;

use super::{Cx, Lower, Unlowered};
use crate::asm::Reg;
use crate::width::{Ext, extend};

pub(super) fn lowering(name: &str) -> Option<Lower> {
    match name {
        "sdiv" => Some(sdiv),
        "udiv" => Some(udiv),
        "srem" => Some(srem),
        "urem" => Some(urem),
        _ => None,
    }
}

/// `%q: iN = sdiv %a, %b`: the quotient rounded towards zero.
fn sdiv(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    divide(cx, op, Ext::Sign, false)
}

/// `%q: iN = udiv %a, %b`.
fn udiv(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    divide(cx, op, Ext::Zero, false)
}

/// `%r: iN = srem %a, %b`: the remainder of `sdiv`, with the sign of `%a`.
fn srem(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    divide(cx, op, Ext::Sign, true)
}

/// `%r: iN = urem %a, %b`.
fn urem(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    divide(cx, op, Ext::Zero, true)
}

/// Loads `%a` into `%rax` and `%b` into `%rcx`, divides them, reading both
/// as `ext` says, and stores the quotient, or the remainder when
/// `remainder` is set, as the result.
fn divide(cx: &mut Cx<'_>, op: &Op, ext: Ext, remainder: bool) -> Result<(), Unlowered> {
    let ([a, b], [r]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err(format!("{} takes two operands and defines one value", op.name).into());
    };
    let w = cx.width(&r.name)?;
    cx.load(Reg::Rax, a)?;
    cx.load(Reg::Rcx, b)?;
    if w == 1 {
        extend(&mut cx.asm, ext, 1, Reg::Rax);
        extend(&mut cx.asm, ext, 1, Reg::Rcx);
    }
    let size = w.max(8);
    let suffix = match size {
        8 => "b",
        16 => "w",
        32 => "l",
        _ => "q",
    };
    let (rax, rdx) = (Reg::Rax, Reg::Rdx);
    match (ext, size) {
        (Ext::Sign, 8) => cx.asm.ins0("cbtw"),
        (Ext::Sign, 16) => cx.asm.ins0("cwtd"),
        (Ext::Sign, 32) => cx.asm.ins0("cltd"),
        (Ext::Sign, _) => cx.asm.ins0("cqto"),
        (Ext::Zero, 8) => cx
            .asm
            .ins("movzbl", format_args!("{}, {}", rax.at(8), rax.at(32))),
        (Ext::Zero, _) => cx
            .asm
            .ins("xorl", format_args!("{}, {}", rdx.at(32), rdx.at(32))),
    }
    let mnemonic = match ext {
        Ext::Sign => "idiv",
        Ext::Zero => "div",
    };
    cx.asm.ins(
        &format!("{mnemonic}{suffix}"),
        format_args!("{}", Reg::Rcx.at(size)),
    );
    let out = match (remainder, size) {
        (false, _) => rax,
        (true, 8) => {
            cx.asm.ins("movb", format_args!("%ah, {}", rax.at(8)));
            rax
        }
        (true, _) => rdx,
    };
    cx.store(&r.name, out)
}
