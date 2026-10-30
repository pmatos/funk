//! Integer widths in registers (ADR-2026-10-30-1231).
//!
//! The backend holds a value of `iN` in one 64-bit register or stack slot:
//! its low `N` bits are the value, and the bits above them are unspecified.
//! An op whose result depends only on its operands' low bits, such as `add`,
//! works on all 64 bits and ignores the rest. An op that reads the bits above
//! `N`, such as a comparison, a right shift, a division or `zext`, first
//! extends those operands with [`extend`]. The same rule holds for
//! arguments and results at a call boundary (ADR-2026-10-30-1232).

use funk_ir::Type;
use funk_ir::dialects::core::{CoreType, core_type};

use crate::asm::{Asm, Reg};

/// The widths that the backend lowers: `i1`, `i8`, `i16`, `i32` and `i64`.
pub const SUPPORTED: [u32; 5] = [1, 8, 16, 32, 64];

/// [`SUPPORTED`], as the diagnostics name it.
const NAMED: &str = "i1, i8, i16, i32 and i64";

/// The width of `ty` if the backend lowers values of it, or why not.
pub fn check(ty: &Type) -> Result<u32, String> {
    match core_type(ty) {
        Some(CoreType::Int(w)) if SUPPORTED.contains(&w) => Ok(w),
        Some(CoreType::Int(128)) => Err(format!(
            "the x86-64 backend does not lower i128 yet: it lowers {NAMED}"
        )),
        _ => Err(format!("the x86-64 backend lowers {NAMED}, not {ty}")),
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
/// `width` is one of [`SUPPORTED`].
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
    fn only_the_five_widths_are_lowered() {
        for w in SUPPORTED {
            assert_eq!(check(&Type::word(format!("i{w}"))), Ok(w));
        }
        for t in ["i7", "i33", "i128", "i16777215", "ptr", "toy.tok"] {
            assert!(check(&Type::word(t)).is_err(), "{t}");
        }
        assert!(
            check(&Type::word("i128"))
                .unwrap_err()
                .contains("not lower i128 yet")
        );
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
