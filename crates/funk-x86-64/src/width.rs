//! Integer widths in registers (ADR-2026-10-30-1231, ADR-2026-11-03-0107).
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
//! in another (ADR-2026-11-03-0107).

use funk_ir::Type;
use funk_ir::dialects::core::{CoreType, core_type};

use crate::asm::{Asm, Reg};

/// The widths that one 64-bit register or slot holds: `i1`, `i8`, `i16`,
/// `i32` and `i64`.
pub const ONE_REGISTER: [u32; 5] = [1, 8, 16, 32, 64];

/// The width that a pair of registers or slots holds: `i128`.
pub const PAIR: u32 = 128;

/// The widths that the backend lowers, as the diagnostics name them.
const NAMED: &str = "i1, i8, i16, i32, i64 and i128";

/// The width of `ty` if the backend lowers values of it, or why not.
pub fn check(ty: &Type) -> Result<u32, String> {
    match core_type(ty) {
        Some(CoreType::Int(w)) if ONE_REGISTER.contains(&w) || w == PAIR => Ok(w),
        _ => Err(format!("the x86-64 backend lowers {NAMED}, not {ty}")),
    }
}

/// The eightbytes that a value of `ty` takes in registers, in slots and on
/// the stack: two for `i128`, and one for any other type, so that a value
/// of a width the backend does not lower still has a slot to name.
pub fn words(ty: &Type) -> usize {
    match core_type(ty) {
        Some(CoreType::Int(PAIR)) => 2,
        _ => 1,
    }
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
    fn only_the_six_widths_are_lowered() {
        for w in ONE_REGISTER.into_iter().chain([PAIR]) {
            assert_eq!(check(&Type::word(format!("i{w}"))), Ok(w));
        }
        for t in ["i7", "i33", "i65", "i127", "i129", "i256", "i16777215"] {
            assert_eq!(
                check(&Type::word(t)),
                Err(format!(
                    "the x86-64 backend lowers i1, i8, i16, i32, i64 and i128, not {t}"
                ))
            );
        }
        for t in ["ptr", "toy.tok"] {
            assert!(check(&Type::word(t)).is_err(), "{t}");
        }
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
