//! How a funk function looks from outside (ADR-2026-10-30-1232): its symbol in the
//! object file, where its arguments arrive and where its result goes, by the
//! System V AMD64 calling convention.

use std::fmt::Write;

use funk_ir::ir::names::is_word;

use crate::asm::{Asm, Mem, Reg};

/// The registers that carry the first six integer arguments, in order.
pub const ARG_REGS: [Reg; 6] = [Reg::Rdi, Reg::Rsi, Reg::Rdx, Reg::Rcx, Reg::R8, Reg::R9];

/// The register that carries an integer result.
pub const RESULT_REG: Reg = Reg::Rax;

/// Emits a complete outgoing call to the funk function `callee`, given
/// its raw fir name and argument slots in parameter order. `%rsp` must be
/// 16-byte aligned, and every source slot is relative to `%rbp`.
///
/// Arguments pass as their slots hold them, without extension. The call
/// restores `%rsp` and leaves the result in [`RESULT_REG`]. The returned
/// byte count is its peak outgoing argument space, padding included, but
/// not the return address: entry stack reservation accounts for that
/// separately. A size error appends no assembly.
///
/// This owns placement and accounting for both fir calls and executable
/// entry code (ADR-2026-11-02-1428).
pub(crate) fn call(asm: &mut Asm, callee: &str, args: &[Mem]) -> Result<u64, String> {
    let bytes = outgoing_bytes(args.len())
        .ok_or("the call passes more arguments on the stack than 2 GiB holds")?;
    let on_stack = args.get(ARG_REGS.len()..).unwrap_or_default();
    if on_stack.len() % 2 == 1 {
        asm.ins("subq", format_args!("$8, %rsp"));
    }
    for slot in on_stack.iter().rev() {
        asm.ins("pushq", format_args!("{slot}"));
    }
    for (reg, slot) in ARG_REGS.iter().zip(args) {
        asm.ins("movq", format_args!("{slot}, {}", reg.q()));
    }
    asm.ins("call", format_args!("{}", symbol(callee)));
    if bytes > 0 {
        asm.ins("addq", format_args!("${bytes}, %rsp"));
    }
    Ok(bytes as u64)
}

/// The 8-byte words that [`call`] pushes for `arguments` arguments before
/// the return address: each argument past the sixth, and a word of padding
/// when there is an odd number of them. The entry's stack figure reads a
/// call by it too (ADR-2026-11-02-1132).
pub(crate) fn pushed_words(arguments: usize) -> usize {
    let stack = arguments.saturating_sub(ARG_REGS.len());
    stack + stack % 2
}

/// The padded outgoing area must fit the signed immediate of `addq`.
fn outgoing_bytes(arguments: usize) -> Option<i32> {
    i32::try_from(pushed_words(arguments).checked_mul(8)?).ok()
}

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

#[cfg(test)]
#[path = "abi/call_tests.rs"]
mod call_tests;
