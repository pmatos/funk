//! Conversions from floats to integers: `fptosi` and `fptoui`
//! (`dialects/core/float_to_int.rs` in `funk-ir`;
//! `docs/decisions/x86-64-backend-lowering-floats.md#conversions-to-integers`),
//! from `f32` and `f64` to `i1` up to `i128`.
//!
//! Both truncate toward zero, and an integer that `iN` does not hold, an
//! infinity or a NaN gives poison. Native code holds no poison, so any
//! value refines it (ADR-2026-10-30-2248): the code must give the exact
//! integer only where the source gives one, and may give anything
//! elsewhere. So it checks a range only where the instruction's own range
//! is narrower than `iN`'s.
//!
//! SSE2's `cvttss2siq` and `cvttsd2siq` truncate toward zero into a signed
//! 64-bit integer, exactly for every float from `-2^63` up to below `2^63`,
//! and give `-2^63` for any other. That covers `fptosi` to every width up
//! to `i64`, and `fptoui` to every width below `i64`: each in-range value
//! is exact, and its low `N` bits are the result, since the bits of a slot
//! above its width are unspecified
//! (`docs/decisions/x86-64-backend.md#values-and-widths`).
//!
//! `fptoui` to `i64` holds values from `2^63` up to below `2^64` too. One at
//! or above `2^63`, by `ucomiss` or `ucomisd`, has `2^63` subtracted first,
//! which is exact by Sterbenz's lemma, since the float is from `2^63` up to
//! below twice that, and gets the top bit back after the conversion.
//!
//! An `i128` has no instruction. An `f32` operand goes to `f64` first, with
//! `cvtss2sd`, which is exact. The code reads the `f64`'s bits: its
//! mantissa with the hidden bit, and its exponent, and shifts the mantissa
//! into `%rdx:%rax`, right for a number below `2^52` and left above, across
//! the halves with `shldq` as a shift at `i128` does. A number below `1`,
//! zeros and subnormals among them, gives `0`. `fptosi` negates the pair
//! when the sign bit is set. An exponent too large for `iN` shifts by a
//! count that the processor masks, and gives some value, which refines
//! the poison of the source. No call is made.
//!
//! M1 has no floating-point exceptions, so no op looks at MXCSR's flags.

use funk_ir::Op;

use super::farith::format;
use super::{Cx, Lower, Unlowered};
use crate::asm::Reg;
use crate::width::{Class, PAIR};

pub(super) fn lowering(name: &str) -> Option<Lower> {
    match name {
        "fptosi" => Some(fptosi),
        "fptoui" => Some(fptoui),
        _ => None,
    }
}

/// `%i: i32 = fptosi %f`.
fn fptosi(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    convert(cx, op, true)
}

/// `%u: i64 = fptoui %d`.
fn fptoui(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    convert(cx, op, false)
}

/// Converts the float `%x` to the integer `%r`, signed when `signed`.
fn convert(cx: &mut Cx<'_>, op: &Op, signed: bool) -> Result<(), Unlowered> {
    let ([x], [r]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err(format!("{} takes one operand and defines one value", op.name).into());
    };
    let (_, mov, suffix) = format(cx, op, x)?;
    if cx.class(&r.name)? == Class::Sse {
        return Err(format!("{} converts a float to an integer", op.name).into());
    }
    let n = cx.width(&r.name)?;
    let sx = cx.slot(x)?;
    cx.asm.ins(mov, format_args!("{sx}, %xmm0"));
    if n == PAIR {
        if suffix == "ss" {
            cx.asm.ins("cvtss2sd", format_args!("%xmm0, %xmm0"));
        }
        pair(cx, signed);
        return cx.store_pair(&r.name, Reg::Rax, Reg::Rdx);
    }
    let cvt = format!("cvtt{suffix}2siq");
    if signed || n < 64 {
        cx.asm.ins(&cvt, format_args!("%xmm0, %rax"));
    } else {
        unsigned64(cx, suffix, &cvt);
    }
    cx.store(&r.name, Reg::Rax)
}

/// Converts the float in `%xmm0`, of the format of `suffix`, to an unsigned
/// 64-bit integer in `%rax`. It clobbers `%rcx` and `%xmm1`.
fn unsigned64(cx: &mut Cx<'_>, suffix: &str, cvt: &str) {
    let (big, done) = (cx.local_label(), cx.local_label());
    // 2^63 in %xmm1.
    if suffix == "ss" {
        cx.asm.ins("movl", format_args!("$0x5f000000, %ecx"));
        cx.asm.ins("movd", format_args!("%ecx, %xmm1"));
    } else {
        cx.asm
            .ins("movabsq", format_args!("$0x43e0000000000000, %rcx"));
        cx.asm.ins("movq", format_args!("%rcx, %xmm1"));
    }
    cx.asm
        .ins(&format!("ucomi{suffix}"), format_args!("%xmm1, %xmm0"));
    cx.asm.ins("jae", format_args!("{big}"));
    cx.asm.ins(cvt, format_args!("%xmm0, %rax"));
    cx.asm.ins("jmp", format_args!("{done}"));
    cx.asm.label(&big);
    cx.asm
        .ins(&format!("sub{suffix}"), format_args!("%xmm1, %xmm0"));
    cx.asm.ins(cvt, format_args!("%xmm0, %rax"));
    cx.asm.ins("btcq", format_args!("$63, %rax"));
    cx.asm.label(&done);
}

/// Converts the `f64` in `%xmm0` to an `i128` in `%rdx:%rax`, signed when
/// `signed`. It clobbers `%rcx` and `%r8`.
fn pair(cx: &mut Cx<'_>, signed: bool) {
    let (left, end) = (cx.local_label(), cx.local_label());
    cx.asm.ins("movq", format_args!("%xmm0, %rax"));
    cx.asm.ins("movq", format_args!("%rax, %r8"));
    // %ecx: the exponent, biased, less the bias and the 52 bits of the
    // mantissa, so the number is the mantissa times 2^%ecx.
    cx.asm.ins("movq", format_args!("%rax, %rcx"));
    cx.asm.ins("shrq", format_args!("$52, %rcx"));
    cx.asm.ins("andl", format_args!("$0x7ff, %ecx"));
    cx.asm.ins("subl", format_args!("$1075, %ecx"));
    // %rax: the mantissa with its hidden bit.
    cx.asm
        .ins("movabsq", format_args!("$0x000fffffffffffff, %rdx"));
    cx.asm.ins("andq", format_args!("%rdx, %rax"));
    cx.asm.ins("btsq", format_args!("$52, %rax"));
    cx.asm.ins("xorl", format_args!("%edx, %edx"));
    cx.asm.ins("testl", format_args!("%ecx, %ecx"));
    cx.asm.ins("jns", format_args!("{left}"));
    // A shift right by more than 63 leaves nothing: %rdx is zero.
    cx.asm.ins("negl", format_args!("%ecx"));
    cx.asm.ins("shrq", format_args!("%cl, %rax"));
    cx.asm.ins("cmpl", format_args!("$63, %ecx"));
    cx.asm.ins("cmovaq", format_args!("%rdx, %rax"));
    cx.asm.ins("jmp", format_args!("{end}"));
    // A shift left of 64 to 127 moves the low half into the high one, as
    // `shift_pair` in `bitwise.rs` does; `movl` keeps the flags.
    cx.asm.label(&left);
    cx.asm.ins("shldq", format_args!("%cl, %rax, %rdx"));
    cx.asm.ins("shlq", format_args!("%cl, %rax"));
    cx.asm.ins("testb", format_args!("$64, %cl"));
    cx.asm.ins("movl", format_args!("$0, %ecx"));
    cx.asm.ins("cmovneq", format_args!("%rax, %rdx"));
    cx.asm.ins("cmovneq", format_args!("%rcx, %rax"));
    cx.asm.label(&end);
    if signed {
        let done = cx.local_label();
        cx.asm.ins("testq", format_args!("%r8, %r8"));
        cx.asm.ins("jns", format_args!("{done}"));
        cx.neg_pair();
        cx.asm.label(&done);
    }
}
