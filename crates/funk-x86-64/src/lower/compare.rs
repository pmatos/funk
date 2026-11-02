//! Comparison and selection: `icmp` and `select` (`dialects/core/compare.rs`
//! in `funk-ir`).
//!
//! `icmp` reads its operands whole, so it first extends each from `N` bits
//! to 64 with [`extend`]: by sign for the signed predicates, and by zero for
//! the unsigned ones and for `eq` and `ne` (ADR-2026-10-30-1231). Then one
//! `cmpq` and the predicate's `setCC` write the result, `0` or `1`, to
//! `%al`, and `%rax` is stored. Bit 0 of the slot is the `i1`; the bits
//! above it, which keep `%a`'s from bit 8 up, are unspecified, as every
//! value's are.
//!
//! `select` tests bit 0 of its condition and nothing above it, and keeps
//! its first value or moves in its second with one `cmovzq`, with no branch
//! (ADR-2026-10-31-0215). The low `N` bits of the chosen slot are the
//! result. Neither op is ever UB, and native code holds no poison
//! (ADR-2026-10-30-2248): where the source gives poison, from a poison
//! operand of `icmp` or a poison condition or chosen value of `select`,
//! any value of the type refines it.

use funk_ir::{Attr, Op};

use super::{Cx, Lower, Unlowered};
use crate::asm::Reg;
use crate::width::{Ext, extend};

pub(super) fn lowering(name: &str) -> Option<Lower> {
    match name {
        "icmp" => Some(icmp),
        "select" => Some(select),
        _ => None,
    }
}

/// How `icmp` reads its operands under each predicate, and the `setCC`
/// that writes whether the predicate holds after `cmpq %b, %a`.
fn predicate(p: &str) -> Option<(Ext, &'static str)> {
    Some(match p {
        "eq" => (Ext::Zero, "sete"),
        "ne" => (Ext::Zero, "setne"),
        "slt" => (Ext::Sign, "setl"),
        "sle" => (Ext::Sign, "setle"),
        "sgt" => (Ext::Sign, "setg"),
        "sge" => (Ext::Sign, "setge"),
        "ult" => (Ext::Zero, "setb"),
        "ule" => (Ext::Zero, "setbe"),
        "ugt" => (Ext::Zero, "seta"),
        "uge" => (Ext::Zero, "setae"),
        _ => return None,
    })
}

/// `%r: i1 = icmp p %a, %b`: whether `p` holds of `%a` and `%b`.
fn icmp(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    let ([a, b], [r]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err("icmp takes two operands and defines one value".into());
    };
    let p = match op.attrs.as_slice() {
        [Attr::Word(p)] => p.as_str(),
        _ => return Err("icmp has one attribute, its predicate".into()),
    };
    let Some((ext, set)) = predicate(p) else {
        return Err(format!("icmp has no predicate {p}").into());
    };
    cx.width(&r.name)?;
    let w = cx.width(a)?;
    cx.load(Reg::Rax, a)?;
    extend(&mut cx.asm, ext, w, Reg::Rax);
    cx.load(Reg::Rcx, b)?;
    extend(&mut cx.asm, ext, w, Reg::Rcx);
    cx.asm
        .ins("cmpq", format_args!("{}, {}", Reg::Rcx.q(), Reg::Rax.q()));
    cx.asm.ins(set, format_args!("{}", Reg::Rax.at(8)));
    cx.store(&r.name, Reg::Rax)
}

/// `%r: iN = select %c, %a, %b`: `%a` when bit 0 of `%c` is set, and `%b`
/// when it is clear.
fn select(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    let ([c, a, b], [r]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err("select takes three operands and defines one value".into());
    };
    cx.width(&r.name)?;
    cx.load(Reg::Rcx, c)?;
    cx.load(Reg::Rax, a)?;
    let b = cx.slot(b)?;
    cx.asm.ins("testb", format_args!("$1, {}", Reg::Rcx.at(8)));
    cx.asm.ins("cmovzq", format_args!("{b}, {}", Reg::Rax.q()));
    cx.store(&r.name, Reg::Rax)
}
