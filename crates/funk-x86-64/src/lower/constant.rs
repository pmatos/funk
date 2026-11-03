//! Constants: `const` (`dialects/core/constant.rs` in `funk-ir`).
//!
//! A constant is written into its slot as a 64-bit immediate: its value read
//! as a signed integer, so its low `N` bits are its bits. `true` is 1 and
//! `false` is 0. An `i128` constant is two immediates, its low and its high
//! 64 bits, one into each of its slots (ADR-2026-11-03-0107).

use funk_ir::{Attr, Op};

use super::{Cx, Lower, Unlowered};
use crate::asm::{Mem, Reg};
use crate::width::PAIR;

pub(super) fn lowering(name: &str) -> Option<Lower> {
    match name {
        "const" => Some(constant),
        _ => None,
    }
}

/// `%c: iN = const v`.
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
