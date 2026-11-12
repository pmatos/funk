//! Width changes: `zext`, `sext` and `trunc` (`dialects/core/width.rs` in
//! `funk-ir`). This file is `cast.rs` because `width` is the module that
//! knows how values sit in registers.
//!
//! A value of `iN` is the low `N` bits of its slot, and the bits above are
//! unspecified (`docs/decisions/x86-64-backend.md#values-and-widths`). So
//! `zext` and `sext` read their operand's top bit and the bits above it:
//! each extends its operand from `M` bits to all 64 with [`width::extend`],
//! by zero or by sign, and the low `N` bits of that are the result. `trunc`
//! reads no bit above `N`: the low `N` bits of its operand's slot are
//! already its result, so it is a copy, whatever the bits above hold.
//!
//! An `i128` result's low half is the operand extended to 64 bits, and its
//! high half is zero for `zext`, and for `sext` 64 copies of the extended
//! value's top bit, which `sarq $63` makes. `trunc` from `i128` copies its
//! operand's low half, whose low `N` bits are the result
//! (`docs/decisions/x86-64-backend-lowering.md#lowering-i128`).

use funk_ir::Op;

use super::{Cx, Lower, Unlowered};
use crate::asm::Reg;
use crate::width::{self, Ext, PAIR};

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
    let n = cx.width(&r.name)?;
    let m = cx.width(x)?;
    cx.load(Reg::Rax, x)?;
    match ext {
        // A `trunc` from `i128` loads its operand's low half.
        None => {}
        Some(_) if m == PAIR => return Err("an i128 extends to no wider width".into()),
        Some(ext) => width::extend(&mut cx.asm, ext, m, Reg::Rax),
    }
    if n != PAIR {
        return cx.store(&r.name, Reg::Rax);
    }
    let (rax, rdx) = (Reg::Rax.q(), Reg::Rdx.q());
    match ext {
        Some(Ext::Zero) => cx.asm.ins("xorl", format_args!("%edx, %edx")),
        Some(Ext::Sign) => {
            cx.asm.ins("movq", format_args!("{rax}, {rdx}"));
            cx.asm.ins("sarq", format_args!("$63, {rdx}"));
        }
        None => return Err("trunc gives no i128".into()),
    }
    cx.store_pair(&r.name, Reg::Rax, Reg::Rdx)
}
