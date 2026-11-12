//! Bit casts: `bitcast` between `f32` and `i32`, and between `f64` and
//! `i64` (`dialects/core/bitcast.rs` in `funk-ir`;
//! `docs/decisions/x86-64-backend-lowering.md#bit-casts`).
//!
//! A float is its bits in one slot, as an integer is, and the bits of either
//! above its width are unspecified
//! (`docs/decisions/x86-64-backend.md#values-and-widths`). So a bit cast is
//! a copy of the slot through `%rax`, in either direction: no SSE
//! instruction runs, so a NaN's sign and payload come through as they are,
//! a signalling NaN's included. An `f16`, `bf16` or `f128` operand or
//! result has a width that the backend reports where it is defined, as for
//! every other float op.

use funk_ir::Op;

use super::{Cx, Lower, Unlowered};
use crate::asm::Reg;

pub(super) fn lowering(name: &str) -> Option<Lower> {
    (name == "bitcast").then_some(bitcast)
}

/// `%b: i32 = bitcast %f` and `%f: f32 = bitcast %b`: `%x`'s slot, copied
/// to the result's.
fn bitcast(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    let ([x], [r]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err("bitcast takes one operand and defines one value".into());
    };
    cx.width(&r.name)?;
    cx.width(x)?;
    cx.load(Reg::Rax, x)?;
    cx.store(&r.name, Reg::Rax)
}
