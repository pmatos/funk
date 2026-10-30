//! Constants: `const` (`dialects/core/constant.rs` in `funk-ir`).
//!
//! A constant is written into its slot as a 64-bit immediate: its value read
//! as a signed integer, so its low `N` bits are its bits. `true` is 1 and
//! `false` is 0.

use funk_ir::{Attr, Op};

use super::{Cx, Lower, Unlowered};
use crate::asm::Reg;

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
    cx.width(&result.name)?;
    let v: i64 = match value {
        Attr::Word(w) if w == "true" => 1,
        Attr::Word(w) if w == "false" => 0,
        Attr::Int(v) => v
            .as_str()
            .parse()
            .map_err(|_| format!("the constant {v} does not fit 64 bits"))?,
        other => return Err(format!("the value of a const is an integer, not {other}").into()),
    };
    let slot = cx.slot(&result.name)?;
    if i32::try_from(v).is_ok() {
        cx.asm.ins("movq", format_args!("${v}, {slot}"));
    } else {
        cx.asm
            .ins("movabsq", format_args!("${v}, {}", Reg::Rax.q()));
        cx.store(&result.name, Reg::Rax)?;
    }
    Ok(())
}
