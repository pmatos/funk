//! Float arithmetic: `fadd`, `fsub`, `fmul`, `fdiv`, `sqrt`, `fneg`,
//! `fabs` and `fma` (`dialects/core/float_arith.rs` in `funk-ir`), at
//! `f32` and `f64`
//! (`docs/decisions/x86-64-backend-lowering.md#float-arithmetic`).
//!
//! Each op that rounds, but `fma`, is one SSE instruction, which rounds to
//! nearest even, as MXCSR's default mode does and as `round(rne)` asks:
//! `movss` or `movsd` loads the first operand into `%xmm0`, and `addss`,
//! `subss`, `mulss`, `divss` or `sqrtss`, or its `sd` form at `f64`, reads
//! the second from its slot. Subnormal operands and results are honoured:
//! nothing sets MXCSR's flush-to-zero or denormals-are-zero bits.
//!
//! `fneg` and `fabs` change only the sign bit, so they work on the bits in
//! `%rax`: `btc` flips bit 31 or 63, and `btr` clears it. That is IEEE
//! 754's negate and abs, also on a NaN, whose result fir lets be any NaN
//! (ADR-2026-11-11-1800).
//!
//! SSE has no fused multiply-add, and FMA3 is not in every x86-64, so
//! `fma` loads its operands into `%xmm0` to `%xmm2` and calls a routine of
//! the runtime helper `fma.s`, which the module's own object file carries,
//! as the one that divides at `i128` (`div.rs`). The routine clobbers only
//! registers that System V lets a callee clobber, none of which holds a
//! value from one op to the next.
//!
//! A result goes to its slot with `movq`, so the bits of an `f32` slot
//! above its 32 are unspecified, as an integer's are. M1 has no
//! floating-point exceptions, so no op looks at MXCSR's flags.

use funk_ir::Op;
use funk_ir::dialects::core::float_format;

use super::{Cx, Lower, Unlowered};
use crate::asm::Reg;
use crate::width::Class;

/// The runtime helper: the routines that do `fma` at `f32` and `f64`, as
/// assembly, which [`super::module`] appends once to a module that calls
/// one.
pub const HELPER: &str = include_str!("fma.s");

/// The bytes of stack that a call of a routine of [`HELPER`] uses below
/// the caller's `%rsp`: its return address, and the word that
/// `__funk_rt_fmaf` pushes or the return address of `__funk_rt_fma`'s
/// call of `.Lrt_fma_unpack`.
pub const HELPER_STACK: u64 = 16;

/// The routine of [`HELPER`] that `op` calls, if it is an `fma` at `f32`
/// or `f64`.
pub fn helper(op: &Op) -> Option<&'static str> {
    if op.name != "fma" {
        return None;
    }
    let [r] = op.results.as_slice() else {
        return None;
    };
    match float_format(&r.ty)? {
        (8, 23) => Some("__funk_rt_fmaf"),
        (11, 52) => Some("__funk_rt_fma"),
        _ => None,
    }
}

pub(super) fn lowering(name: &str) -> Option<Lower> {
    match name {
        "fadd" | "fsub" | "fmul" | "fdiv" => Some(binary),
        "sqrt" => Some(sqrt),
        "fneg" => Some(fneg),
        "fabs" => Some(fabs),
        "fma" => Some(fma),
        _ => None,
    }
}

/// The width of the float `name`, 32 or 64, the instruction that loads it
/// into an SSE register, and the suffix of its SSE instructions: `movss`
/// and `ss`, or `movsd` and `sd`.
fn format(
    cx: &Cx<'_>,
    op: &Op,
    name: &str,
) -> Result<(u32, &'static str, &'static str), Unlowered> {
    if cx.class(name)? != Class::Sse {
        return Err(format!("{} works on floats", op.name).into());
    }
    match cx.width(name)? {
        32 => Ok((32, "movss", "ss")),
        64 => Ok((64, "movsd", "sd")),
        w => Err(format!("{} works on f32 or f64, not a value of {w} bits", op.name).into()),
    }
}

/// `%r: f32 = fadd round(rne) %a, %b`, and `fsub`, `fmul` and `fdiv`
/// likewise: `%a` in `%xmm0`, then the instruction on `%b`'s slot.
fn binary(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    let ([a, b], [r]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err(format!("{} takes two operands and defines one value", op.name).into());
    };
    let (_, mov, suffix) = format(cx, op, a)?;
    let ins = match op.name.as_str() {
        "fadd" => "add",
        "fsub" => "sub",
        "fmul" => "mul",
        _ => "div",
    };
    let (sa, sb, sr) = (cx.slot(a)?, cx.slot(b)?, cx.slot(&r.name)?);
    cx.asm.ins(mov, format_args!("{sa}, %xmm0"));
    cx.asm
        .ins(&format!("{ins}{suffix}"), format_args!("{sb}, %xmm0"));
    cx.asm.ins("movq", format_args!("%xmm0, {sr}"));
    Ok(())
}

/// `%r: f64 = sqrt round(rne) %a`: `sqrtss` or `sqrtsd` of `%a`'s slot.
fn sqrt(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    let ([a], [r]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err("sqrt takes one operand and defines one value".into());
    };
    let (_, _, suffix) = format(cx, op, a)?;
    let (sa, sr) = (cx.slot(a)?, cx.slot(&r.name)?);
    cx.asm
        .ins(&format!("sqrt{suffix}"), format_args!("{sa}, %xmm0"));
    cx.asm.ins("movq", format_args!("%xmm0, {sr}"));
    Ok(())
}

/// Applies `ins`, `btcq` or `btrq`, to the sign bit of the one operand of
/// `op`, and stores the result.
fn sign_bit(cx: &mut Cx<'_>, op: &Op, ins: &str) -> Result<(), Unlowered> {
    let ([a], [r]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err(format!("{} takes one operand and defines one value", op.name).into());
    };
    let (w, _, _) = format(cx, op, a)?;
    cx.load(Reg::Rax, a)?;
    cx.asm.ins(ins, format_args!("${}, %rax", w - 1));
    cx.store(&r.name, Reg::Rax)
}

/// `%r: f32 = fneg %a`: `%a` with its sign bit flipped.
fn fneg(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    sign_bit(cx, op, "btcq")
}

/// `%r: f32 = fabs %a`: `%a` with its sign bit cleared.
fn fabs(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    sign_bit(cx, op, "btrq")
}

/// `%r: f64 = fma round(rne) %a, %b, %c`: a call of the helper's routine
/// with the operands in `%xmm0`, `%xmm1` and `%xmm2`.
fn fma(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    let ([a, b, c], [r]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err("fma takes three operands and defines one value".into());
    };
    let (_, mov, _) = format(cx, op, a)?;
    let routine = helper(op).ok_or("fma at f32 or f64 calls the runtime helper")?;
    for (n, x) in [a, b, c].into_iter().enumerate() {
        let slot = cx.slot(x)?;
        cx.asm.ins(mov, format_args!("{slot}, %xmm{n}"));
    }
    cx.asm.ins("call", format_args!("{routine}"));
    let sr = cx.slot(&r.name)?;
    cx.asm.ins("movq", format_args!("%xmm0, {sr}"));
    Ok(())
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
    /// and push as much as they pop.
    #[test]
    fn the_helper_touches_only_caller_saved_registers() {
        let saved = ["bx", "bl", "bh", "bp", "r12", "r13", "r14", "r15"];
        for line in code() {
            for reg in saved {
                assert!(!line.contains(&format!("%{reg}")), "{line}");
                assert!(!line.contains(&format!("%e{reg}")), "{line}");
                assert!(!line.contains(&format!("%r{reg}")), "{line}");
            }
            for xmm in 3..16 {
                assert!(!line.contains(&format!("%xmm{xmm}")), "{line}");
            }
        }
        let count = |m: &str| code().filter(|l| l.trim_start().starts_with(m)).count();
        assert_eq!(count("pushq"), count("popq"));
    }

    /// Every label is a local `__funk_rt_` symbol, or starts with
    /// `.Lrt_fma`, which no block's or function's local label does.
    #[test]
    fn the_helper_s_labels_stay_apart_from_the_module_s() {
        let labels: Vec<&str> = code()
            .filter_map(|l| l.strip_suffix(':'))
            .filter(|l| !l.starts_with(char::is_whitespace))
            .collect();
        for label in &labels {
            assert!(
                label.starts_with("__funk_rt_") || label.starts_with(".Lrt_fma"),
                "{label}"
            );
            assert_ne!(crate::abi::symbol(label), *label);
        }
        assert!(labels.contains(&"__funk_rt_fmaf") && labels.contains(&"__funk_rt_fma"));
        assert!(!code().any(|l| l.contains(".globl")));
    }

    /// The routines go no deeper than [`HELPER_STACK`] says:
    /// `__funk_rt_fmaf` pushes one word and calls nothing, `__funk_rt_fma`
    /// pushes nothing and calls only `.Lrt_fma_unpack`, which, from its
    /// label to the end of the file, pushes and calls nothing.
    #[test]
    fn the_helper_s_stack_is_its_return_address_and_one_word() {
        let lines: Vec<&str> = code().map(str::trim).collect();
        let at = |label: &str| lines.iter().position(|l| *l == label).unwrap();
        let (fmaf, fma, unpack) = (
            at("__funk_rt_fmaf:"),
            at("__funk_rt_fma:"),
            at(".Lrt_fma_unpack:"),
        );
        assert!(fmaf < fma && fma < unpack);
        let count = |part: &[&str], m: &str| part.iter().filter(|l| l.starts_with(m)).count();
        let (f32s, f64s, leaf) = (&lines[fmaf..fma], &lines[fma..unpack], &lines[unpack..]);
        assert_eq!((count(f32s, "pushq"), count(f32s, "call")), (1, 0));
        assert_eq!(count(f64s, "pushq"), 0);
        for call in f64s.iter().filter(|l| l.starts_with("call")) {
            assert!(call.ends_with(".Lrt_fma_unpack"), "{call}");
        }
        assert_eq!((count(leaf, "pushq"), count(leaf, "call")), (0, 0));
        assert_eq!(HELPER_STACK, 8 + 8);
    }
}
