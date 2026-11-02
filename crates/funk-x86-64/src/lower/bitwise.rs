//! Bitwise ops and shifts: `and`, `or`, `xor`, `shl`, `lshr` and `ashr`
//! (`dialects/core/bitwise.rs` in `funk-ir`).
//!
//! Bit `i` of `and`, `or` and `xor` depends only on bit `i` of each operand,
//! so one 64-bit `andq`, `orq` or `xorq` computes the op at every width,
//! whatever the bits above `N` hold (ADR-2026-10-30-1231).
//!
//! A shift is one 64-bit `shlq`, `shrq` or `sarq` by `%cl`. Its amount is
//! read as unsigned, so it is first zero-extended from `N` bits. The low `N`
//! bits of `shl` depend only on the low `N` bits of its value, but a right
//! shift brings the bits above `N` down, so `lshr` zero-extends its value
//! and `ashr` sign-extends it (ADR-2026-10-30-1231). x86 masks the count of
//! a 64-bit shift to its low 6 bits. An amount below `N` is below 64, so the
//! mask keeps it: every shift by less than `N` is exact, at every width,
//! `i1` included, where the only such amount is `0`. No code tests the
//! amount: a shift by `N` or more gives poison, which any value of the type
//! refines (ADR-2026-10-29-2008), so it gives whatever the masked shift
//! gives (ADR-2026-10-30-2248).

use funk_ir::Op;

use super::arith::binary;
use super::{Cx, Lower, Unlowered};
use crate::asm::Reg;
use crate::width::{Ext, extend};

pub(super) fn lowering(name: &str) -> Option<Lower> {
    match name {
        "and" => Some(and),
        "or" => Some(or),
        "xor" => Some(xor),
        "shl" => Some(shl),
        "lshr" => Some(lshr),
        "ashr" => Some(ashr),
        _ => None,
    }
}

/// `%r: iN = and %a, %b`.
fn and(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    binary(cx, op, "andq")
}

/// `%r: iN = or %a, %b`.
fn or(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    binary(cx, op, "orq")
}

/// `%r: iN = xor %a, %b`.
fn xor(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    binary(cx, op, "xorq")
}

/// `%r: iN = shl %a, %n`: `%a` shifted left by `%n`, filling with zeros.
fn shl(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    shift(cx, op, None, "shlq")
}

/// `%r: iN = lshr %a, %n`: `%a` shifted right by `%n`, filling with zeros.
fn lshr(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    shift(cx, op, Some(Ext::Zero), "shrq")
}

/// `%r: iN = ashr %a, %n`: `%a` shifted right by `%n`, filling with copies
/// of its sign bit.
fn ashr(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    shift(cx, op, Some(Ext::Sign), "sarq")
}

/// Loads `%a` into `%rax` and extends it by `ext`, if any, loads `%n` into
/// `%rcx` and zero-extends it, applies `mnemonic` by `%cl`, and stores
/// `%rax` as the result.
fn shift(cx: &mut Cx<'_>, op: &Op, ext: Option<Ext>, mnemonic: &str) -> Result<(), Unlowered> {
    let ([a, n], [r]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err(format!("{} takes two operands and defines one value", op.name).into());
    };
    let w = cx.width(&r.name)?;
    cx.load(Reg::Rax, a)?;
    if let Some(ext) = ext {
        extend(&mut cx.asm, ext, w, Reg::Rax);
    }
    cx.load(Reg::Rcx, n)?;
    extend(&mut cx.asm, Ext::Zero, w, Reg::Rcx);
    cx.asm.ins(
        mnemonic,
        format_args!("{}, {}", Reg::Rcx.at(8), Reg::Rax.q()),
    );
    cx.store(&r.name, Reg::Rax)
}
