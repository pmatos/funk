//! Conversions between float formats: `fpext` from `f32` to `f64` and
//! `fptrunc` from `f64` to `f32` (`dialects/core/float_convert.rs` in
//! `funk-ir`;
//! `docs/decisions/x86-64-backend-lowering-floats.md#conversions-between-formats`).
//!
//! Each is one SSE2 instruction on the operand's slot: `cvtss2sd`, which is
//! exact, and `cvtsd2ss`, which rounds as MXCSR says, and its default mode
//! is round to nearest even, as `round(rne)` asks. Each keeps the sign of a
//! zero and an infinity, honours subnormals, since nothing sets MXCSR's
//! flush-to-zero or denormals-are-zero bits, gives an infinity of its sign
//! on overflow and a zero of its sign on underflow. A NaN gives a quiet NaN,
//! which fir lets be any NaN (ADR-2026-11-09-1549).
//!
//! The result goes to its slot with `movq`, so the bits of an `f32` slot
//! above its 32 are unspecified. Every other pair of formats has an `f16`,
//! `bf16` or `f128` side, whose width the backend reports where it is
//! defined, as for every other float op. M1 has no floating-point
//! exceptions, so no op looks at MXCSR's flags.

use funk_ir::Op;

use super::farith::format;
use super::{Cx, Lower, Unlowered};

pub(super) fn lowering(name: &str) -> Option<Lower> {
    matches!(name, "fpext" | "fptrunc").then_some(convert)
}

/// `%d: f64 = fpext %f` and `%f: f32 = fptrunc round(rne) %d`: one
/// conversion of `%x`'s slot into `%xmm0`.
fn convert(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    let ([x], [r]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err(format!("{} takes one operand and defines one value", op.name).into());
    };
    let (_, _, from) = format(cx, op, x)?;
    let (_, _, to) = format(cx, op, &r.name)?;
    let ins = match (from, to) {
        ("ss", "sd") => "cvtss2sd",
        ("sd", "ss") => "cvtsd2ss",
        _ => return Err(format!("{} converts between f32 and f64", op.name).into()),
    };
    let (sx, sr) = (cx.slot(x)?, cx.slot(&r.name)?);
    cx.asm.ins(ins, format_args!("{sx}, %xmm0"));
    cx.asm.ins("movq", format_args!("%xmm0, {sr}"));
    Ok(())
}
