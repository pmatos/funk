//! Integer widths in registers (ADR-2026-10-30-1231, ADR-2026-11-03-010730).
//!
//! The backend holds a value of `iN`, `N` at most 64, in one 64-bit
//! register or stack slot: its low `N` bits are the value, and the bits
//! above them are unspecified. An op whose result depends only on its
//! operands' low bits, such as `add`, works on all 64 bits and ignores the
//! rest. An op that reads the bits above `N`, such as a comparison, a right
//! shift, `zext`, or a division at `i1` (ADR-2026-10-31-0050), first extends
//! those operands with [`extend`]. The same rule holds for the arguments a
//! funk function receives and the results it returns (ADR-2026-10-30-1232).
//!
//! A value of `i128` is a pair of eightbytes, each 64 bits of the value with
//! none unspecified: the low eightbyte in one register or slot, the high one
//! in another (ADR-2026-11-03-010730).
//!
//! A value of `f32` or `f64` is its bits, in the low 32 or 64 bits of one
//! slot or SSE register, the bits above unspecified, as for an `iN`
//! (ADR-2026-11-11-1140). [`check`] gives its width, 32 or 64, and
//! [`class`] says that it passes in SSE registers.

use funk_ir::Type;
use funk_ir::dialects::core::{CoreType, core_type};

use crate::asm::{Asm, Reg};

/// The widths that one 64-bit register or slot holds: `i1`, `i8`, `i16`,
/// `i32` and `i64`.
pub const ONE_REGISTER: [u32; 5] = [1, 8, 16, 32, 64];

/// The width that a pair of registers or slots holds: `i128`.
pub const PAIR: u32 = 128;

/// The float formats that the backend lowers, `f32` and `f64`, as
/// `(e, m, bits)`.
const FLOATS: [(u32, u32, u32); 2] = [(8, 23, 32), (11, 52, 64)];

/// The types that the backend lowers, as the diagnostics name them.
const NAMED: &str = "i1, i8, i16, i32, i64, i128, f32 and f64";

/// The width of `ty` if the backend lowers values of it, or why not: `N`
/// for `iN`, and the bits of a float, 32 for `f32` and 64 for `f64`.
pub fn check(ty: &Type) -> Result<u32, String> {
    lowered(ty).0
}

/// [`check`] and [`class`] of `ty`, from one decoding of it.
pub fn lowered(ty: &Type) -> (Result<u32, String>, Class) {
    let t = core_type(ty);
    let width = match t {
        Some(CoreType::Int(w)) if ONE_REGISTER.contains(&w) || w == PAIR => Some(w),
        Some(CoreType::Float { e, m }) => FLOATS.iter().find(|f| (f.0, f.1) == (e, m)).map(|f| f.2),
        _ => None,
    };
    let width = width.ok_or_else(|| format!("the x86-64 backend lowers {NAMED}, not {ty}"));
    (width, class_of(t))
}

/// How a value passes to and from a function, by System V's classes
/// (ADR-2026-11-11-1140).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Class {
    /// One eightbyte of class INTEGER: `i1` to `i64`.
    Int,
    /// Two eightbytes of class INTEGER, low half first: `i128`.
    Pair,
    /// One eightbyte of class SSE: `f32` or `f64`.
    Sse,
}

impl Class {
    /// The eightbytes that a value of this class takes.
    pub fn words(self) -> usize {
        match self {
            Class::Pair => 2,
            Class::Int | Class::Sse => 1,
        }
    }
}

/// The class of a value of `ty`: SSE for a float, a pair for `i128`, and
/// one INTEGER eightbyte for any other type, so that a value of a type the
/// backend does not lower still has a slot to name.
pub fn class(ty: &Type) -> Class {
    class_of(core_type(ty))
}

fn class_of(t: Option<CoreType>) -> Class {
    match t {
        Some(CoreType::Float { .. }) => Class::Sse,
        Some(CoreType::Int(PAIR)) => Class::Pair,
        _ => Class::Int,
    }
}

/// The eightbytes that a value of `ty` takes in registers, in slots and on
/// the stack: two for `i128`, and one for any other type, so that a value
/// of a width the backend does not lower still has a slot to name.
pub fn words(ty: &Type) -> usize {
    class(ty).words()
}

/// How to fill the bits above a value's width.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ext {
    /// Copy the value's top bit: the value read as a signed integer.
    Sign,
    /// Clear them: the value read as an unsigned integer.
    Zero,
}

/// Extends the `width`-bit value in the low bits of `reg` to all 64 bits.
/// `width` is one of [`ONE_REGISTER`].
pub fn extend(asm: &mut Asm, ext: Ext, width: u32, reg: Reg) {
    let (q, l) = (reg.q(), reg.at(32));
    match (ext, width) {
        (_, 64) => {}
        (Ext::Sign, 1) => {
            asm.ins("shlq", format_args!("$63, {q}"));
            asm.ins("sarq", format_args!("$63, {q}"));
        }
        (Ext::Zero, 1) => asm.ins("andl", format_args!("$1, {l}")),
        (Ext::Sign, 32) => asm.ins("movslq", format_args!("{l}, {q}")),
        (Ext::Zero, 32) => asm.ins("movl", format_args!("{l}, {l}")),
        (Ext::Sign, w) => {
            let mnemonic = if w == 8 { "movsbq" } else { "movswq" };
            asm.ins(mnemonic, format_args!("{}, {q}", reg.at(w)));
        }
        (Ext::Zero, w) => {
            let mnemonic = if w == 8 { "movzbl" } else { "movzwl" };
            asm.ins(mnemonic, format_args!("{}, {l}", reg.at(w)));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn only_the_six_widths_and_two_float_formats_are_lowered() {
        for w in ONE_REGISTER.into_iter().chain([PAIR]) {
            assert_eq!(check(&Type::word(format!("i{w}"))), Ok(w));
        }
        assert_eq!(check(&Type::word("f32")), Ok(32));
        assert_eq!(check(&Type::word("f64")), Ok(64));
        for t in [
            "i7",
            "i33",
            "i65",
            "i127",
            "i129",
            "i256",
            "i16777215",
            "f16",
            "bf16",
            "f128",
        ] {
            assert_eq!(
                check(&Type::word(t)),
                Err(format!(
                    "the x86-64 backend lowers i1, i8, i16, i32, i64, i128, f32 and f64, not {t}"
                ))
            );
        }
        for t in ["ptr", "toy.tok"] {
            assert!(check(&Type::word(t)).is_err(), "{t}");
        }
    }

    #[test]
    fn floats_pass_in_sse_registers() {
        assert_eq!(class(&Type::word("f32")), Class::Sse);
        assert_eq!(class(&Type::word("f64")), Class::Sse);
        assert_eq!(class(&Type::word("bf16")), Class::Sse);
        assert_eq!(class(&Type::word("i128")), Class::Pair);
        assert_eq!(class(&Type::word("i64")), Class::Int);
        assert_eq!(words(&Type::word("f64")), 1);
    }

    #[test]
    fn only_i128_takes_two_eightbytes() {
        assert_eq!(words(&Type::word("i128")), 2);
        for t in ["i1", "i64", "i65", "i129", "i256", "ptr"] {
            assert_eq!(words(&Type::word(t)), 1, "{t}");
        }
    }

    #[test]
    fn extension_fills_the_high_bits() {
        let lines = |ext, w| {
            let mut a = Asm::new();
            extend(&mut a, ext, w, Reg::Rax);
            a.finish()
        };
        assert_eq!(lines(Ext::Sign, 64), "");
        assert_eq!(lines(Ext::Zero, 64), "");
        assert_eq!(
            lines(Ext::Sign, 1),
            "\tshlq\t$63, %rax\n\tsarq\t$63, %rax\n"
        );
        assert_eq!(lines(Ext::Zero, 1), "\tandl\t$1, %eax\n");
        assert_eq!(lines(Ext::Sign, 8), "\tmovsbq\t%al, %rax\n");
        assert_eq!(lines(Ext::Zero, 16), "\tmovzwl\t%ax, %eax\n");
        assert_eq!(lines(Ext::Sign, 32), "\tmovslq\t%eax, %rax\n");
        assert_eq!(lines(Ext::Zero, 32), "\tmovl\t%eax, %eax\n");
    }
}
