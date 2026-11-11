//! Constants: `const` and `poison` (`dialects/core/constant.rs` in
//! `funk-ir`).
//!
//! A constant is written into its slot as a 64-bit immediate: its value read
//! as a signed integer, so its low `N` bits are its bits. `true` is 1 and
//! `false` is 0. A float constant at `f32` or `f64` is a float literal
//! (ADR-2026-11-11-1438), read into its bits, and is written as an integer
//! of those bits: SSE has no immediate operands, and the slot is what an op
//! reads (ADR-2026-11-11-1140). An `i128` constant is two immediates, its low and its high
//! 64 bits, one into each of its slots (ADR-2026-11-03-010730).
//!
//! Native code holds no poison (ADR-2026-10-30-2248), and any value refines
//! it, so `poison` writes zero into every eightbyte of its slot: one at
//! `i1` to `i64`, two at `i128`. Zero is a value of every width, `false`
//! at `i1`, and the same on every run, so what native code gives for a
//! poison never depends on what a slot held before (ADR-2026-11-03-1616).

use funk_ir::dialects::core::{float_format, read_float};
use funk_ir::{Attr, Op};

use super::{Cx, Lower, Unlowered};
use crate::asm::{Mem, Reg};
use crate::width::PAIR;

pub(super) fn lowering(name: &str) -> Option<Lower> {
    match name {
        "const" => Some(constant),
        "poison" => Some(poison),
        _ => None,
    }
}

/// `%c: iN = const v`, and `%c: f32 = const v` or `%c: f64 = const v`.
fn constant(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    let ([result], [value]) = (op.results.as_slice(), op.attrs.as_slice()) else {
        return Err("const defines one value and has one attribute".into());
    };
    let w = cx.width(&result.name)?;
    let v: i128 = match value {
        Attr::Word(w) if w == "true" => 1,
        Attr::Word(w) if w == "false" => 0,
        Attr::Int(v) => v
            .as_str()
            .parse()
            .map_err(|_| format!("the constant {v} does not fit 128 bits"))?,
        Attr::Float(s) => {
            let (e, m) = float_format(&result.ty).ok_or("a float literal defines a float")?;
            // Verification has checked that `s` is the spelling of its bits.
            match read_float(e, m, s) {
                Some(bits) => bits as i128,
                None => return Err(format!("{s} is no constant of {}", result.ty).into()),
            }
        }
        other => return Err(format!("the value of a const is an integer, not {other}").into()),
    };
    let slot = cx.slot(&result.name)?;
    // A valid constant of at most 64 bits fits an `i64`, so its low 64
    // bits are the whole of it.
    immediate(cx, slot, v as i64);
    if w == PAIR {
        immediate(cx, slot.high(), (v >> 64) as i64);
    }
    Ok(())
}

/// `%p: iN = poison`: zero in each eightbyte.
fn poison(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    let ([result], []) = (op.results.as_slice(), op.attrs.as_slice()) else {
        return Err("poison defines one value and has no attribute".into());
    };
    cx.width(&result.name)?;
    for slot in cx.eightbytes(&result.name)? {
        immediate(cx, slot, 0);
    }
    Ok(())
}

/// Writes the 64 bits `v` into `slot`: with one `movq` when they are a
/// sign-extended 32-bit immediate, and through `%rax` otherwise.
fn immediate(cx: &mut Cx<'_>, slot: Mem, v: i64) {
    if i32::try_from(v).is_ok() {
        cx.asm.ins("movq", format_args!("${v}, {slot}"));
    } else {
        cx.asm
            .ins("movabsq", format_args!("${v}, {}", Reg::Rax.q()));
        cx.asm.ins("movq", format_args!("{}, {slot}", Reg::Rax.q()));
    }
}
