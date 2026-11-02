//! Calls: `call` (`dialects/core/call.rs` in `funk-ir`).
//!
//! A call between funk functions follows System V (ADR-2026-10-30-1232).
//! The arguments past the sixth go on the stack: when there is an odd
//! number of them, 8 bytes of padding first, then each argument pushed
//! from its slot, the last first, so that the seventh is at `(%rsp)` when
//! the call is made. Then the first six are loaded into `%rdi`, `%rsi`,
//! `%rdx`, `%rcx`, `%r8` and `%r9`, the call goes to the callee's symbol
//! (ADR-2026-10-30-1232), the caller pops what it pushed, and stores
//! `%rax` in the slot of the result, if there is one. A frame is a
//! multiple of 16 bytes (ADR-2026-10-30-1230) and the stack arguments are
//! padded to an even number, so `%rsp` is 16-byte aligned at the call.
//!
//! No argument is extended: each goes as its slot holds it, since a funk
//! callee reads only the low `N` bits of an `iN` argument, and the result
//! comes back the same way (ADR-2026-11-02-1021). Every value lives in its
//! slot, not in a register, and a funk function writes no callee-saved
//! register but `%rbp`, which it restores, so nothing needs saving around
//! the call. A call with more than one result needs the convention of #31;
//! until then it is reported at the call.

use funk_ir::{Attr, Op};

use super::{Cx, Lower, Unlowered};
use crate::abi::{ARG_REGS, RESULT_REG, symbol};

pub(super) fn lowering(name: &str) -> Option<Lower> {
    match name {
        "call" => Some(call),
        _ => None,
    }
}

/// `%r = call @f %a, %b`.
fn call(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    let [Attr::Sym(callee)] = op.attrs.as_slice() else {
        return Err("call names its callee by one symbol".into());
    };
    if op.results.len() > 1 {
        return Err(format!(
            "call returns {} values: the x86-64 backend returns at most one value so far",
            op.results.len()
        )
        .into());
    }
    for x in &op.operands {
        cx.width(x)?;
    }
    for d in &op.results {
        cx.width(&d.name)?;
    }
    let on_stack = op.operands.get(ARG_REGS.len()..).unwrap_or_default();
    let pad = on_stack.len() % 2 == 1;
    let pushed = (on_stack.len() + usize::from(pad))
        .checked_mul(8)
        .and_then(|n| i32::try_from(n).ok())
        .ok_or("the call passes more arguments on the stack than 2 GiB holds")?;
    if pad {
        cx.asm.ins("subq", format_args!("$8, %rsp"));
    }
    for x in on_stack.iter().rev() {
        let slot = cx.slot(x)?;
        cx.asm.ins("pushq", format_args!("{slot}"));
    }
    for (reg, x) in ARG_REGS.iter().zip(&op.operands) {
        cx.load(*reg, x)?;
    }
    cx.asm.ins("call", format_args!("{}", symbol(callee)));
    if pushed > 0 {
        cx.asm.ins("addq", format_args!("${pushed}, %rsp"));
    }
    if let [r] = op.results.as_slice() {
        cx.store(&r.name, RESULT_REG)?;
    }
    Ok(())
}
