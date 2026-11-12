//! Division and remainder: `sdiv`, `udiv`, `srem` and `urem`
//! (`dialects/core/div.rs` in `funk-ir`;
//! `docs/decisions/x86-64-backend-lowering.md#division`).
//!
//! Each op is one `idiv` (`sdiv`, `srem`) or `div` (`udiv`, `urem`) of the
//! op's own size: `b`, `w`, `l` or `q` for `i8`, `i16`, `i32` and `i64`.
//! The divisor is `%rcx` at that size, which reads only the value's bits.
//! The dividend is `%rax` at that size, widened into the high half that the
//! instruction also reads: by sign with `cbtw`, `cwtd`, `cltd` or `cqto`,
//! by zero with `movzbl %al, %eax`, which clears `%ah`, or with
//! `xorl %edx, %edx`. The quotient is in `%al`, `%ax`, `%eax` or `%rax`;
//! the remainder in `%ah`, `%dx`, `%edx` or `%rdx`. `i1` has no division of
//! its own: both operands are extended to 64 bits
//! (`docs/decisions/x86-64-backend.md#values-and-widths`) and divided as
//! `i8`.
//!
//! No code tests the divisor. A zero divisor, and the signed minimum
//! divided by `-1`, are immediate UB in the source, so whatever `idiv` or
//! `div` does on them, a trap included, is correct. A broken `exact` gives
//! poison, which any value refines (ADR-2026-10-29-2008), so `exact`
//! lowers as the plain quotient (ADR-2026-10-30-2248).
//!
//! No instruction divides 128 bits by 128 bits, so each op at `i128` is a
//! call of a routine of the runtime helper `div128.s`, which the module's
//! own object file carries
//! (`docs/decisions/x86-64-backend-lowering.md#division-at-i128`). The call
//! passes the operands and takes the result as System V passes and returns
//! an `__int128`, and the routine clobbers only registers that System V
//! lets a callee clobber, none of which holds a value from one op to the
//! next (`docs/decisions/x86-64-backend-lowering.md#division-at-i128`).

use funk_ir::Op;
use funk_ir::dialects::core::{CoreType, core_type};

use super::{Cx, Lower, Unlowered};
use crate::asm::Reg;
use crate::width::{Ext, PAIR, extend};

/// The runtime helper: the routines that divide at `i128`, as assembly,
/// which [`super::module`] appends once to a module that calls one.
pub const HELPER: &str = include_str!("div128.s");

/// The bytes of stack that a call of a routine of [`HELPER`] uses below
/// the caller's `%rsp`: its return address, the sign that
/// `__funk_rt_sdiv128` and `__funk_rt_srem128` push, and their call of
/// `__funk_rt_udivmod128` or `__funk_rt_magnitudes`.
pub const HELPER_STACK: u64 = 24;

/// The routine of [`HELPER`] that `op` calls, if it is a division at
/// `i128`.
pub fn helper(op: &Op) -> Option<&'static str> {
    let routine = match op.name.as_str() {
        "sdiv" => "__funk_rt_sdiv128",
        "udiv" => "__funk_rt_udiv128",
        "srem" => "__funk_rt_srem128",
        "urem" => "__funk_rt_urem128",
        _ => return None,
    };
    let [r] = op.results.as_slice() else {
        return None;
    };
    (core_type(&r.ty) == Some(CoreType::Int(PAIR))).then_some(routine)
}

pub(super) fn lowering(name: &str) -> Option<Lower> {
    match name {
        "sdiv" => Some(sdiv),
        "udiv" => Some(udiv),
        "srem" => Some(srem),
        "urem" => Some(urem),
        _ => None,
    }
}

/// `%q: iN = sdiv %a, %b`: the quotient rounded towards zero.
fn sdiv(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    divide(cx, op, Ext::Sign, false)
}

/// `%q: iN = udiv %a, %b`.
fn udiv(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    divide(cx, op, Ext::Zero, false)
}

/// `%r: iN = srem %a, %b`: the remainder of `sdiv`, with the sign of `%a`.
fn srem(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    divide(cx, op, Ext::Sign, true)
}

/// `%r: iN = urem %a, %b`.
fn urem(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    divide(cx, op, Ext::Zero, true)
}

/// Loads `%a` into `%rax` and `%b` into `%rcx`, divides them, reading both
/// as `ext` says, and stores the quotient, or the remainder when
/// `remainder` is set, as the result. At `i128` it loads `%a` into
/// `%rsi:%rdi` and `%b` into `%rcx:%rdx`, calls the op's routine of
/// [`HELPER`], and stores `%rdx:%rax`.
fn divide(cx: &mut Cx<'_>, op: &Op, ext: Ext, remainder: bool) -> Result<(), Unlowered> {
    let ([a, b], [r]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err(format!("{} takes two operands and defines one value", op.name).into());
    };
    let w = cx.width(&r.name)?;
    if let Some(routine) = helper(op) {
        cx.load_pair(Reg::Rdi, Reg::Rsi, a)?;
        cx.load_pair(Reg::Rdx, Reg::Rcx, b)?;
        cx.asm.ins("call", format_args!("{routine}"));
        return cx.store_pair(&r.name, Reg::Rax, Reg::Rdx);
    }
    cx.load(Reg::Rax, a)?;
    cx.load(Reg::Rcx, b)?;
    if w == 1 {
        extend(&mut cx.asm, ext, 1, Reg::Rax);
        extend(&mut cx.asm, ext, 1, Reg::Rcx);
    }
    let size = w.max(8);
    let suffix = match size {
        8 => "b",
        16 => "w",
        32 => "l",
        _ => "q",
    };
    let (rax, rdx) = (Reg::Rax, Reg::Rdx);
    match (ext, size) {
        (Ext::Sign, 8) => cx.asm.ins0("cbtw"),
        (Ext::Sign, 16) => cx.asm.ins0("cwtd"),
        (Ext::Sign, 32) => cx.asm.ins0("cltd"),
        (Ext::Sign, _) => cx.asm.ins0("cqto"),
        (Ext::Zero, 8) => cx
            .asm
            .ins("movzbl", format_args!("{}, {}", rax.at(8), rax.at(32))),
        (Ext::Zero, _) => cx
            .asm
            .ins("xorl", format_args!("{}, {}", rdx.at(32), rdx.at(32))),
    }
    let mnemonic = match ext {
        Ext::Sign => "idiv",
        Ext::Zero => "div",
    };
    cx.asm.ins(
        &format!("{mnemonic}{suffix}"),
        format_args!("{}", Reg::Rcx.at(size)),
    );
    let out = match (remainder, size) {
        (false, _) => rax,
        (true, 8) => {
            cx.asm.ins("movb", format_args!("%ah, {}", rax.at(8)));
            rax
        }
        (true, _) => rdx,
    };
    cx.store(&r.name, out)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The helper's code: each line without its comment.
    fn code() -> impl Iterator<Item = &'static str> {
        HELPER
            .lines()
            .map(|l| l.split('#').next().unwrap_or_default())
    }

    /// The routines touch no register that System V makes a callee save,
    /// at any size, and push as much as they pop
    /// (`docs/decisions/x86-64-backend-lowering.md#division-at-i128`).
    #[test]
    fn the_helper_touches_only_caller_saved_registers() {
        let saved = ["bx", "bl", "bh", "bp", "r12", "r13", "r14", "r15"];
        for line in code() {
            for reg in saved {
                assert!(!line.contains(&format!("%{reg}")), "{line}");
                assert!(!line.contains(&format!("%e{reg}")), "{line}");
                assert!(!line.contains(&format!("%r{reg}")), "{line}");
            }
            assert!(!line.contains("%rsp") && !line.contains("%esp"), "{line}");
        }
        let count = |m: &str| code().filter(|l| l.trim_start().starts_with(m)).count();
        assert_eq!(count("pushq"), count("popq"));
    }

    /// Every label is a local `__funk_rt_` symbol, which no fir function's
    /// symbol is, or starts with `.Lrt_div128_`, which no block's or
    /// function's local label does
    /// (`docs/decisions/x86-64-backend-lowering.md#division-at-i128`).
    #[test]
    fn the_helper_s_labels_stay_apart_from_the_module_s() {
        let labels: Vec<&str> = code()
            .filter_map(|l| l.strip_suffix(':'))
            .filter(|l| !l.starts_with(char::is_whitespace))
            .collect();
        assert_eq!(labels.len(), 9, "{labels:?}");
        for label in labels {
            assert!(
                label.starts_with("__funk_rt_") || label.starts_with(".Lrt_div128_"),
                "{label}"
            );
            assert_ne!(crate::abi::symbol(label), label);
        }
        assert!(!code().any(|l| l.contains(".globl")));
        for routine in ["sdiv", "udiv", "srem", "urem"] {
            let name = format!("__funk_rt_{routine}128:");
            assert!(code().any(|l| l == name), "{name}");
        }
    }
}
