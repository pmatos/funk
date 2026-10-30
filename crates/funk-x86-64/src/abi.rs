//! How a funk function looks from outside (ADR-2026-10-30-1232): its symbol in the
//! object file, where its arguments arrive and where its result goes, by the
//! System V AMD64 calling convention.

use std::fmt::Write;

use funk_ir::ir::names::is_word;

use crate::asm::Reg;

/// The registers that carry the first six integer arguments, in order.
pub const ARG_REGS: [Reg; 6] = [Reg::Rdi, Reg::Rsi, Reg::Rdx, Reg::Rcx, Reg::R8, Reg::R9];

/// The register that carries an integer result.
pub const RESULT_REG: Reg = Reg::Rax;

/// The offset from `%rbp`, after the standard prologue, of argument `i`
/// when it is passed on the stack: `i >= 6`. The return address is at
/// `8(%rbp)`, and stack arguments follow it, 8 bytes each.
pub fn stack_arg_offset(i: usize) -> Option<i32> {
    let slot = i.checked_sub(ARG_REGS.len())?;
    i32::try_from(slot).ok()?.checked_mul(8)?.checked_add(16)
}

/// The symbol of the fir function `name` in the object file.
///
/// A word that starts with a letter is its own symbol: letters, digits, `_`
/// and `.`, as fir writes it unquoted. Any other name becomes `__funk_sym_`
/// followed by its UTF-8 bytes in lower-case hexadecimal. That includes
/// every name that starts with `_`, which C reserves for its implementation
/// and which the toolchain uses: `ld` defines `_end` and `__bss_start`
/// itself, and `as` treats `_GLOBAL_OFFSET_TABLE_` apart. So the mapping is
/// one-to-one, no symbol it gives collides with the toolchain's or with the
/// runtime's `__funk` symbols, and GNU `as` and the ELF symbol table take
/// each one as it is.
pub fn symbol(name: &str) -> String {
    if is_word(name) && !name.starts_with('_') {
        return name.to_string();
    }
    let mut out = String::from("__funk_sym_");
    for b in name.bytes() {
        let _ = write!(out, "{b:02x}");
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn words_are_their_own_symbols() {
        for name in ["seven", "add3", "acc.1", "main", "rax", "etext", "x_"] {
            assert_eq!(symbol(name), name);
        }
    }

    #[test]
    fn other_names_are_spelled_in_hexadecimal() {
        assert_eq!(symbol(""), "__funk_sym_");
        assert_eq!(symbol("1"), "__funk_sym_31");
        assert_eq!(symbol("a b"), "__funk_sym_612062");
        assert_eq!(symbol("é"), "__funk_sym_c3a9");
        assert_eq!(
            symbol("_ZN3foo$LT$E"),
            "__funk_sym_5f5a4e33666f6f244c542445"
        );
        assert_eq!(
            symbol("__funk_sym_31"),
            "__funk_sym_5f5f66756e6b5f73796d5f3331"
        );
        assert_eq!(symbol("_end"), "__funk_sym_5f656e64");
        assert_eq!(symbol("_start.v2"), "__funk_sym_5f73746172742e7632");
    }

    #[test]
    fn stack_arguments_follow_the_return_address() {
        assert_eq!(stack_arg_offset(5), None);
        assert_eq!(stack_arg_offset(6), Some(16));
        assert_eq!(stack_arg_offset(9), Some(40));
        assert_eq!(stack_arg_offset(usize::MAX), None);
    }
}
