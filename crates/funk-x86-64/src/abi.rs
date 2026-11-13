//! How a funk function looks from outside (ADR-2026-10-30-1232): its symbol in the
//! object file, where its arguments arrive and, in [`results`], where its
//! results go (ADR-2026-10-30-1232), by the System V AMD64 calling convention.
//! An `i128` passes as two eightbytes
//! (`docs/decisions/x86-64-backend-abi.md#arguments`), and an `f32` or `f64` in an
//! SSE register (`docs/decisions/x86-64-backend-abi.md#floats-in-sse-registers`);
//! `layout.rs` says where each one goes.

mod layout;

use std::fmt::Write;

use funk_ir::ir::names::is_word;

pub(crate) use layout::{Loc, layout};

use crate::asm::{Asm, Mem, Reg};
use crate::width::Class;

pub mod results;

/// The registers that carry the first six integer arguments, in order.
pub const ARG_REGS: [Reg; 6] = [Reg::Rdi, Reg::Rsi, Reg::Rdx, Reg::Rcx, Reg::R8, Reg::R9];

/// The register that carries an integer result, or the low half of an
/// `i128` result; [`results`] says where the others go.
pub const RESULT_REG: Reg = Reg::Rax;

/// An argument of a funk call: the slot that holds it, relative to
/// `%rbp`, and its class: a pair for an `i128`, whose high half is in the
/// slot above ([`Mem::high`]), SSE for a float, and one INTEGER eightbyte
/// for any other value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Arg {
    pub slot: Mem,
    pub class: Class,
}

/// Stores a function's incoming arguments in their frame slots after the
/// standard prologue has established `%rbp`. `args` gives the declared
/// parameters in order, each of its class. `hidden` is the slot
/// for the result-area address, when results return in memory; it arrives
/// first, in `%rdi`, and shifts the parameters along the shared layout.
///
/// Every eightbyte is stored as it arrives, without extension, low half
/// first for an `i128`. Stack arguments are read above the saved `%rbp`
/// and return address, through `%rax`; `%rsp` does not change. Destination
/// slots must be valid frame slots. An unencodable incoming stack offset
/// returns the zero-based index into `args` for the caller's diagnostic;
/// earlier stores remain in `asm`.
pub(crate) fn receive(asm: &mut Asm, args: &[Arg], hidden: Option<Mem>) -> Result<(), usize> {
    let skip = usize::from(hidden.is_some());
    let classes = passed(skip, args.iter().map(|a| a.class));
    let incoming = layout(&classes);
    if let Some(slot) = hidden {
        asm.ins("movq", format_args!("{}, {slot}", ARG_REGS[0].q()));
    }
    for (i, (arg, locs)) in args
        .iter()
        .zip(incoming.args.into_iter().skip(skip))
        .enumerate()
    {
        for (loc, to) in locs.into_iter().zip([arg.slot, arg.slot.high()]) {
            match loc {
                Loc::Reg(reg) => asm.ins("movq", format_args!("{}, {to}", reg.q())),
                Loc::Xmm(n) => asm.ins("movq", format_args!("%xmm{n}, {to}")),
                Loc::Stack(at) => {
                    let from = Mem {
                        disp: stack_arg_offset(at).ok_or(i)?,
                    };
                    asm.ins("movq", format_args!("{from}, %rax"));
                    asm.ins("movq", format_args!("%rax, {to}"));
                }
            }
        }
    }
    Ok(())
}

/// Emits a complete outgoing call to the funk function `callee`, given
/// its raw fir name and its arguments in parameter order. `%rsp` must be
/// 16-byte aligned.
///
/// Arguments pass as their slots hold them, without extension, where
/// [`layout`] puts them: the eightbytes on the stack are pushed from the
/// top down, a hole of padding as a `subq`, then the registers are loaded.
/// When the results go in memory, the first argument is the address of the
/// result area, of one eightbyte (ADR-2026-10-30-1232). The call restores
/// `%rsp` and leaves the results where [`results`] puts them. The returned
/// byte count is its peak outgoing argument space, padding included, but
/// not the return address: entry stack reservation accounts for that
/// separately. A size error appends no assembly.
///
/// This owns placement and accounting for both fir calls and executable
/// entry code
/// (`docs/decisions/x86-64-backend-abi.md#one-emitter-for-funk-calls`).
pub(crate) fn call(asm: &mut Asm, callee: &str, args: &[Arg]) -> Result<u64, String> {
    let classes: Vec<Class> = args.iter().map(|a| a.class).collect();
    let layout = layout(&classes);
    let bytes = outgoing_bytes(layout.stack)
        .ok_or("the call passes more arguments on the stack than 2 GiB holds")?;
    let mut stack = vec![None; layout.stack / 8];
    let mut regs = Vec::new();
    for (a, locs) in args.iter().zip(&layout.args) {
        for (loc, slot) in locs.iter().zip([a.slot, a.slot.high()]) {
            match *loc {
                Loc::Stack(at) => stack[at / 8] = Some(slot),
                Loc::Reg(reg) => regs.push((reg.q().to_string(), slot)),
                Loc::Xmm(n) => regs.push((format!("%xmm{n}"), slot)),
            }
        }
    }
    let mut hole = 0;
    for word in stack.iter().rev() {
        match word {
            None => hole += 8,
            Some(slot) => {
                if hole > 0 {
                    asm.ins("subq", format_args!("${hole}, %rsp"));
                    hole = 0;
                }
                asm.ins("pushq", format_args!("{slot}"));
            }
        }
    }
    for (reg, slot) in regs {
        asm.ins("movq", format_args!("{slot}, {reg}"));
    }
    asm.ins("call", format_args!("{}", symbol(callee)));
    if bytes > 0 {
        asm.ins("addq", format_args!("${bytes}, %rsp"));
    }
    Ok(bytes as u64)
}

/// The class of each argument of a call, in the order that [`layout`]
/// places them: `hidden` arguments of one INTEGER eightbyte first, which is the
/// address of the result area when the results go in memory
/// ([`results::Layout::hidden_arguments`], ADR-2026-10-30-1232), then each
/// of `args`. The address takes `%rdi`, so an `i128` argument looks for its
/// pair of registers from `%rsi` on. The callee's prologue reads its
/// incoming arguments by this; [`call`] gets the address as its first [`Arg`].
pub(crate) fn passed(hidden: usize, args: impl IntoIterator<Item = Class>) -> Vec<Class> {
    std::iter::repeat_n(Class::Int, hidden)
        .chain(args)
        .collect()
}

/// The padded outgoing area of `bytes` must fit the signed immediate of
/// `addq`.
fn outgoing_bytes(bytes: usize) -> Option<i32> {
    i32::try_from(bytes).ok()
}

/// The offset from `%rbp`, after the standard prologue, of the eightbyte of
/// an argument that the caller put `at` bytes above `%rsp` at the call
/// ([`Loc::Stack`]). The return address is at `8(%rbp)`, and the stack
/// arguments start at `16(%rbp)`.
pub fn stack_arg_offset(at: usize) -> Option<i32> {
    i32::try_from(at).ok()?.checked_add(16)
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
        assert_eq!(stack_arg_offset(0), Some(16));
        assert_eq!(stack_arg_offset(24), Some(40));
        assert_eq!(stack_arg_offset(i32::MAX as usize - 16), Some(i32::MAX));
        assert_eq!(stack_arg_offset(i32::MAX as usize - 15), None);
        assert_eq!(stack_arg_offset(usize::MAX), None);
    }
}

#[cfg(test)]
#[path = "abi/call_tests.rs"]
mod call_tests;

#[cfg(test)]
#[path = "abi/incoming_tests.rs"]
mod incoming_tests;
