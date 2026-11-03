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
//!
//! At `i128` (ADR-2026-11-03-0107), `and`, `or` and `xor` apply to each
//! half. A shift reads its amount's low half only: an amount below 128 is
//! that half, and any other gives poison. The value's halves are shifted
//! together by `%cl` with `shldq` or `shrdq`, which move bits from one half
//! into the other, and the half they fill is shifted with `shlq`, `shrq` or
//! `sarq`. x86 masks those counts to 6 bits, so that is the shift by the
//! amount modulo 64. When bit 6 of `%cl` is set, the amount is 64 or more
//! and the halves must move one place further: two `cmovneq` put the
//! shifted half into the other, and fill it with zeros or, for `ashr`, the
//! sign. No code branches on the amount, and an amount of 128 or more gives
//! whatever that sequence gives for its low 7 bits.

use funk_ir::Op;

use super::arith::{binary, halves};
use super::{Cx, Lower, Unlowered, is_pair};
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
    each_bit(cx, op, "andq")
}

/// `%r: iN = or %a, %b`.
fn or(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    each_bit(cx, op, "orq")
}

/// `%r: iN = xor %a, %b`.
fn xor(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    each_bit(cx, op, "xorq")
}

/// `mnemonic` on the operands, or at `i128` on each of their halves.
fn each_bit(cx: &mut Cx<'_>, op: &Op, mnemonic: &str) -> Result<(), Unlowered> {
    if is_pair(cx, op)? {
        return halves(cx, op, mnemonic, mnemonic);
    }
    binary(cx, op, mnemonic)
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
    if is_pair(cx, op)? {
        return shift_pair(cx, op, ext);
    }
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

/// [`shift`] at `i128`: `%a` in `%rdx:%rax`, shifted by the low half of
/// `%n` in `%rcx`. `shl` moves bits up, from `%rax` into `%rdx`; `lshr`
/// (`ext` zero) and `ashr` (`ext` sign) move them down, from `%rdx` into
/// `%rax`, filling with zeros or with the sign, which `%rsi` holds.
fn shift_pair(cx: &mut Cx<'_>, op: &Op, ext: Option<Ext>) -> Result<(), Unlowered> {
    let ([a, n], [r]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err(format!("{} takes two operands and defines one value", op.name).into());
    };
    let (rax, rdx, rsi) = (Reg::Rax.q(), Reg::Rdx.q(), Reg::Rsi.q());
    let cl = Reg::Rcx.at(8);
    cx.load_pair(Reg::Rax, Reg::Rdx, a)?;
    cx.load(Reg::Rcx, n)?;
    // `from` is the half that moves into `into` when the amount is 64 or
    // more; `into` then takes `from` and `from` takes the fill in `%rsi`.
    let (from, into) = match ext {
        None => {
            cx.asm.ins("shldq", format_args!("{cl}, {rax}, {rdx}"));
            cx.asm.ins("shlq", format_args!("{cl}, {rax}"));
            cx.asm.ins("xorl", format_args!("%esi, %esi"));
            (rax, rdx)
        }
        Some(ext) => {
            cx.asm.ins("shrdq", format_args!("{cl}, {rdx}, {rax}"));
            if ext == Ext::Sign {
                cx.asm.ins("movq", format_args!("{rdx}, {rsi}"));
                cx.asm.ins("sarq", format_args!("$63, {rsi}"));
                cx.asm.ins("sarq", format_args!("{cl}, {rdx}"));
            } else {
                cx.asm.ins("shrq", format_args!("{cl}, {rdx}"));
                cx.asm.ins("xorl", format_args!("%esi, %esi"));
            }
            (rdx, rax)
        }
    };
    cx.asm.ins("testb", format_args!("$64, {cl}"));
    cx.asm.ins("cmovneq", format_args!("{from}, {into}"));
    cx.asm.ins("cmovneq", format_args!("{rsi}, {from}"));
    cx.store_pair(&r.name, Reg::Rax, Reg::Rdx)
}
