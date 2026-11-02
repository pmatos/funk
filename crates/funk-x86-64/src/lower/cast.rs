//! Width changes: `zext`, `sext` and `trunc` (`dialects/core/width.rs` in
//! `funk-ir`). This file is `cast.rs` because `width` is the module that
//! knows how values sit in registers.
//!
//! A value of `iN` is the low `N` bits of its slot, and the bits above are
//! unspecified (ADR-2026-10-30-1231). So `zext` and `sext` read their
//! operand's top bit and the bits above it: each extends its operand from
//! `M` bits to all 64 with [`width::extend`], by zero or by sign, and the
//! low `N` bits of that are the result. `trunc` reads no bit above `N`: the
//! low `N` bits of its operand's slot are already its result, so it is a
//! copy, whatever the bits above hold.

use funk_ir::Op;

use super::{Cx, Lower, Unlowered};
use crate::asm::Reg;
use crate::width::{self, Ext};

pub(super) fn lowering(name: &str) -> Option<Lower> {
    match name {
        "zext" => Some(zext),
        "sext" => Some(sext),
        "trunc" => Some(trunc),
        _ => None,
    }
}

/// `%w: iN = zext %x`: `%x` with zeros above its `M` bits.
fn zext(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    change(cx, op, Some(Ext::Zero))
}

/// `%w: iN = sext %x`: `%x` with copies of its top bit above its `M` bits.
fn sext(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    change(cx, op, Some(Ext::Sign))
}

/// `%w: iN = trunc %x`: the low `N` bits of `%x`.
fn trunc(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    change(cx, op, None)
}

/// Loads `%x` into `%rax`, extends it from its width by `ext` if there is
/// one, and stores `%rax` as the result.
fn change(cx: &mut Cx<'_>, op: &Op, ext: Option<Ext>) -> Result<(), Unlowered> {
    let ([x], [r]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err(format!("{} takes one operand and defines one value", op.name).into());
    };
    cx.width(&r.name)?;
    let m = cx.width(x)?;
    cx.load(Reg::Rax, x)?;
    if let Some(ext) = ext {
        width::extend(&mut cx.asm, ext, m, Reg::Rax);
    }
    cx.store(&r.name, Reg::Rax)
}
