//! Conversions from integers to floats: `sitofp` and `uitofp`
//! (`dialects/core/int_to_float.rs` in `funk-ir`;
//! `docs/decisions/x86-64-backend-lowering.md#conversions-from-integers`),
//! from `i1` to `i128` to `f32` and `f64`.
//!
//! SSE2's `cvtsi2ssq` and `cvtsi2sdq` convert a signed 64-bit integer,
//! rounded as MXCSR says, and its default mode is round to nearest even, as
//! `round(rne)` asks. So an operand of at most 64 bits is extended to 64,
//! by sign for `sitofp` and by zero for `uitofp`
//! (`docs/decisions/x86-64-backend.md#values-and-widths`), and converted
//! with one instruction. An unsigned value below `2^63` is a signed value
//! too.
//!
//! An unsigned 64-bit value of `2^63` or more is halved first, with the bit
//! it drops ORed back into its lowest bit: the halved value has 63 bits,
//! more than the 24 or 53 that the result keeps and the one below them that
//! rounding reads, so its lowest bit records only whether anything below
//! was set. It converts, rounded once, and adding the result to itself
//! doubles it exactly.
//!
//! An `i128` has no instruction. `sitofp` takes the magnitude of a negative
//! operand, converts it as unsigned and flips the sign bit of the result. An
//! unsigned value below `2^64` converts as above; any other is shifted left
//! until the high half's top bit is set, the high half keeps the bits that
//! matter, and its lowest bit records whether the low half has any set. It
//! is halved and converted as above, and the result, rounded once, is
//! multiplied by the power of two that the shifts took off, which is exact
//! unless it overflows, and then gives the infinity that rounding to nearest
//! gives. No call is made.
//!
//! The result goes to its slot with `movq`, so the bits of an `f32` slot
//! above its 32 are unspecified. M1 has no floating-point exceptions, so no
//! op looks at MXCSR's flags.

use funk_ir::Op;

use super::{Cx, Lower, Unlowered};
use crate::asm::Reg;
use crate::width::{self, Class, Ext, PAIR};

pub(super) fn lowering(name: &str) -> Option<Lower> {
    match name {
        "sitofp" => Some(sitofp),
        "uitofp" => Some(uitofp),
        _ => None,
    }
}

/// `%f: f32 = sitofp round(rne) %i`.
fn sitofp(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    convert(cx, op, true)
}

/// `%f: f64 = uitofp round(rne) %i`.
fn uitofp(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    convert(cx, op, false)
}

/// The result's format: its width, the suffix of its SSE instructions,
/// `ss` or `sd`, and the bits of its mantissa and its exponent bias, from
/// which a power of two is built.
struct Format {
    bits: u32,
    suffix: &'static str,
    mantissa: u32,
    bias: u32,
}

/// Converts the integer `%x` to the float `%r`, reading `%x` as signed when
/// `signed`.
fn convert(cx: &mut Cx<'_>, op: &Op, signed: bool) -> Result<(), Unlowered> {
    let ([x], [r]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err(format!("{} takes one operand and defines one value", op.name).into());
    };
    if cx.class(&r.name)? != Class::Sse || cx.class(x)? == Class::Sse {
        return Err(format!("{} converts an integer to a float", op.name).into());
    }
    let f = match cx.width(&r.name)? {
        32 => Format {
            bits: 32,
            suffix: "ss",
            mantissa: 23,
            bias: 127,
        },
        64 => Format {
            bits: 64,
            suffix: "sd",
            mantissa: 52,
            bias: 1023,
        },
        w => return Err(format!("{} gives f32 or f64, not {w} bits", op.name).into()),
    };
    let n = cx.width(x)?;
    if n == PAIR {
        cx.load_pair(Reg::Rax, Reg::Rdx, x)?;
        pair(cx, &f, signed);
    } else {
        cx.load(Reg::Rax, x)?;
        let ext = if signed { Ext::Sign } else { Ext::Zero };
        width::extend(&mut cx.asm, ext, n, Reg::Rax);
        if signed || n < 64 {
            cx.asm
                .ins(&format!("cvtsi2{}q", f.suffix), format_args!("%rax, %xmm0"));
        } else {
            let done = cx.local_label();
            unsigned64(cx, &f, &done);
            cx.asm.label(&done);
        }
    }
    let sr = cx.slot(&r.name)?;
    cx.asm.ins("movq", format_args!("%xmm0, {sr}"));
    Ok(())
}

/// Converts the unsigned 64-bit value in `%rax` into `%xmm0`, and goes on
/// at `done`. It clobbers `%rax` and `%rcx`.
fn unsigned64(cx: &mut Cx<'_>, f: &Format, done: &str) {
    let cvt = format!("cvtsi2{}q", f.suffix);
    let half = cx.local_label();
    cx.asm.ins("testq", format_args!("%rax, %rax"));
    cx.asm.ins("js", format_args!("{half}"));
    cx.asm.ins(&cvt, format_args!("%rax, %xmm0"));
    cx.asm.ins("jmp", format_args!("{done}"));
    cx.asm.label(&half);
    halve_and_convert(cx, f, Reg::Rax, Reg::Rcx);
    cx.asm
        .ins(&format!("add{}", f.suffix), format_args!("%xmm0, %xmm0"));
    cx.asm.ins("jmp", format_args!("{done}"));
}

/// Converts `top / 2`, with the bit that the halving drops ORed into the
/// lowest bit, into `%xmm0`. `top` holds an unsigned value whose top bit is
/// set; the halved value goes through `scratch`, and both are clobbered.
fn halve_and_convert(cx: &mut Cx<'_>, f: &Format, top: Reg, scratch: Reg) {
    let (t, s) = (top.q(), scratch.q());
    cx.asm.ins("movq", format_args!("{t}, {s}"));
    cx.asm.ins("shrq", format_args!("$1, {s}"));
    cx.asm.ins("andl", format_args!("$1, {}", top.at(32)));
    cx.asm.ins("orq", format_args!("{t}, {s}"));
    cx.asm
        .ins(&format!("cvtsi2{}q", f.suffix), format_args!("{s}, %xmm0"));
}

/// Converts the `i128` in `%rdx:%rax`, signed when `signed`, into `%xmm0`.
/// It clobbers `%rax`, `%rcx`, `%rdx`, `%r8` and `%xmm1`.
fn pair(cx: &mut Cx<'_>, f: &Format, signed: bool) {
    let (done, big) = (cx.local_label(), cx.local_label());
    if signed {
        // The sign stays in %r8; a negative value becomes its magnitude.
        let positive = cx.local_label();
        cx.asm.ins("movq", format_args!("%rdx, %r8"));
        cx.asm.ins("testq", format_args!("%rdx, %rdx"));
        cx.asm.ins("jns", format_args!("{positive}"));
        cx.asm.ins("negq", format_args!("%rax"));
        cx.asm.ins("adcq", format_args!("$0, %rdx"));
        cx.asm.ins("negq", format_args!("%rdx"));
        cx.asm.label(&positive);
    }
    cx.asm.ins("testq", format_args!("%rdx, %rdx"));
    cx.asm.ins("jnz", format_args!("{big}"));
    unsigned64(cx, f, &done);
    cx.asm.label(&big);
    // %cl: the leading zeros of the high half, which the shifts take off.
    cx.asm.ins("bsrq", format_args!("%rdx, %rcx"));
    cx.asm.ins("xorl", format_args!("$63, %ecx"));
    cx.asm.ins("shldq", format_args!("%cl, %rax, %rdx"));
    cx.asm.ins("shlq", format_args!("%cl, %rax"));
    // The low half's bits, as one bit: 1 when any is set.
    cx.asm.ins("negq", format_args!("%rax"));
    cx.asm.ins("sbbq", format_args!("%rax, %rax"));
    cx.asm.ins("andl", format_args!("$1, %eax"));
    cx.asm.ins("orq", format_args!("%rax, %rdx"));
    halve_and_convert(cx, f, Reg::Rdx, Reg::Rax);
    // The value is the converted one times 2^(65 - %cl): build that power
    // of two's bits in %rcx, and multiply.
    cx.asm.ins("negl", format_args!("%ecx"));
    cx.asm.ins("addl", format_args!("${}, %ecx", f.bias + 65));
    cx.asm.ins("shlq", format_args!("${}, %rcx", f.mantissa));
    cx.asm.ins("movq", format_args!("%rcx, %xmm1"));
    cx.asm
        .ins(&format!("mul{}", f.suffix), format_args!("%xmm1, %xmm0"));
    cx.asm.label(&done);
    if signed {
        let end = cx.local_label();
        cx.asm.ins("testq", format_args!("%r8, %r8"));
        cx.asm.ins("jns", format_args!("{end}"));
        cx.asm.ins("movq", format_args!("%xmm0, %rax"));
        cx.asm.ins("btcq", format_args!("${}, %rax", f.bits - 1));
        cx.asm.ins("movq", format_args!("%rax, %xmm0"));
        cx.asm.label(&end);
    }
}
