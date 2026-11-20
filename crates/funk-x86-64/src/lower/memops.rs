//! Copies, moves and sets: `memcpy`, `memmove` and `memset`
//! (`dialects/core/memcopy.rs` and `memset.rs` in `funk-ir`;
//! `docs/decisions/x86-64-backend-lowering-memory.md#copies-moves-and-sets`).
//!
//! Each op is a call of funk's own routine of the runtime helper
//! `memops.s`, which the module's own object file carries, as the `i128`
//! division routines are carried (ADR-2026-11-09-1551). The routines are
//! local `__funk_rt_` symbols, so a program that only copies, moves or sets
//! memory links with no C library, and one that also links it never
//! clashes with its `memcpy`, `memmove` or `memset`.
//!
//! The pointers are of a memory that the backend realises, 8-bit units and
//! 64-bit pointers (`memory.rs`), so a unit is a byte and a length in units
//! is a length in bytes. A pointer of any other memory is reported where it
//! is defined, so no op of it reaches here. The call passes the destination
//! in `%rdi`, the source, or `memset`'s `i8` value, in `%rsi`, and the
//! length in `%rdx`, read as unsigned: zero-extended from its width, since
//! a slot's bits above a value's width are unspecified. An `i128` length
//! whose high half is not zero saturates to `2^64 - 1`, as an `alloca`'s
//! count past 64 bits does: no native allocation holds 2^64 bytes, so
//! such a length is UB, and the routine runs until it faults rather than
//! copy the length's low half and return. A
//! poison length is whatever bits the slot holds, one of the lengths that
//! the spec chooses from (the human's ruling of 2026-11-19 on #234), and a
//! poison `memset` value writes whatever byte it holds, which refines
//! poison units. The ordering, `nonatomic` alone, needs no code.

use funk_ir::Op;

use super::{Cx, Lower, Unlowered};
use crate::asm::Reg;
use crate::width::{self, Ext, PAIR};

/// The runtime helper: funk's own `memcpy`, `memmove` and `memset`, as
/// assembly, which [`super::module`] appends once to a module that calls
/// one.
pub const HELPER: &str = include_str!("memops.s");

/// The bytes of stack that a call of a routine of [`HELPER`] uses below
/// the caller's `%rsp`: its return address.
pub const HELPER_STACK: u64 = 8;

/// The routine of [`HELPER`] that the op named `name` calls, if any.
fn routine(name: &str) -> Option<&'static str> {
    match name {
        "memcpy" => Some("__funk_rt_memcpy"),
        "memmove" => Some("__funk_rt_memmove"),
        "memset" => Some("__funk_rt_memset"),
        _ => None,
    }
}

/// The routine of [`HELPER`] that `op` calls, if it is a copy, a move or a
/// set.
pub fn helper(op: &Op) -> Option<&'static str> {
    routine(&op.name)
}

pub(super) fn lowering(name: &str) -> Option<Lower> {
    routine(name).map(|_| call as Lower)
}

/// `memcpy nonatomic %d, %s, %n`, `memmove nonatomic %d, %s, %n` and
/// `memset nonatomic %d, %v, %n`: a call of the op's routine.
fn call(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    let ([d, s, n], []) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err(format!("{} takes three operands and defines nothing", op.name).into());
    };
    let routine = helper(op).ok_or("a copy, move or set calls the runtime helper")?;
    cx.width(d)?;
    cx.width(s)?;
    let w = cx.width(n)?;
    cx.load(Reg::Rdi, d)?;
    cx.load(Reg::Rsi, s)?;
    if w == PAIR {
        cx.load_pair(Reg::Rdx, Reg::Rax, n)?;
        cx.asm.ins("movq", format_args!("$-1, %rcx"));
        cx.asm.ins("testq", format_args!("%rax, %rax"));
        cx.asm.ins("cmovnzq", format_args!("%rcx, %rdx"));
    } else {
        cx.load(Reg::Rdx, n)?;
        width::extend(&mut cx.asm, Ext::Zero, w, Reg::Rdx);
    }
    cx.asm.ins("call", format_args!("{routine}"));
    Ok(())
}

#[cfg(test)]
mod tests {
    use funk_ir::{Registry, parse};

    use super::*;

    /// The helper's code: each line without its comment, trimmed.
    fn code() -> Vec<&'static str> {
        HELPER
            .lines()
            .map(|l| l.split('#').next().unwrap_or_default().trim())
            .collect()
    }

    fn lowered(func: &str) -> Result<String, Vec<funk_ir::Diagnostic>> {
        let text = format!("{func}\n\nlocs {{\n  @0 = unknown\n}}\n");
        let m = parse(&text, &Registry::core()).unwrap();
        super::super::module(&m).map(|l| l.text)
    }

    /// The routines touch no general register but `%rax`, `%rcx`, `%rsi`
    /// and `%rdi`, which System V lets a callee clobber, read `%rdx`, push
    /// nothing, call nothing, and clear the direction flag after each
    /// time they set it.
    #[test]
    fn the_helper_touches_only_caller_saved_registers() {
        for line in code() {
            for reg in line.split('%').skip(1) {
                let reg: String = reg
                    .chars()
                    .take_while(char::is_ascii_alphanumeric)
                    .collect();
                assert!(
                    ["rax", "eax", "rcx", "rdx", "rsi", "esi", "rdi"].contains(&reg.as_str()),
                    "{line}"
                );
            }
            assert!(!line.starts_with("call") && !line.starts_with("push"));
        }
        let count = |m: &str| code().iter().filter(|l| **l == m).count();
        assert_eq!((count("std"), count("cld")), (1, 1));
        let lines = code();
        let std = lines.iter().position(|l| *l == "std").unwrap();
        assert_eq!(lines[std + 1..std + 4], ["rep movsb", "cld", "ret"]);
        assert_eq!(HELPER_STACK, 8);
    }

    /// Every label is a local `__funk_rt_` symbol, which no fir function's
    /// symbol is, or starts with `.Lrt_mem_`, which no block's or
    /// function's local label does.
    #[test]
    fn the_helper_s_labels_stay_apart_from_the_module_s() {
        let lines = code();
        let labels: Vec<&str> = lines.iter().filter_map(|l| l.strip_suffix(':')).collect();
        assert_eq!(labels.len(), 4, "{labels:?}");
        for label in &labels {
            assert!(
                label.starts_with("__funk_rt_") || label.starts_with(".Lrt_mem_"),
                "{label}"
            );
            assert_ne!(crate::abi::symbol(label), *label);
        }
        assert!(!lines.iter().any(|l| l.contains(".globl")));
        for op in ["memcpy", "memmove", "memset"] {
            let name = format!("__funk_rt_{op}:");
            assert!(lines.contains(&name.as_str()), "{name}");
        }
    }

    #[test]
    fn each_op_calls_its_routine_with_its_length_zero_extended() {
        let asm = lowered(
            "func @f(%d: ptr, %s: ptr, %v: i8, %a: i1, %b: i8, %c: i16, %e: i32, \
             %g: i64) {\n^entry:\n  memcpy nonatomic %d, %s, %a @0\n  \
             memmove nonatomic %d, %s, %b @0\n  memset nonatomic %d, %v, %c @0\n  \
             memcpy nonatomic %d, %s, %e @0\n  memmove nonatomic %d, %s, %g @0\n  \
             ret @0\n}",
        )
        .unwrap();
        for (ext, routine) in [
            ("\tandl\t$1, %edx\n", "memcpy"),
            ("\tmovzbl\t%dl, %edx\n", "memmove"),
            ("\tmovzwl\t%dx, %edx\n", "memset"),
            ("\tmovl\t%edx, %edx\n", "memcpy"),
            ("\tmovq\t-64(%rbp), %rdx\n", "memmove"),
        ] {
            let call = format!("{ext}\tcall\t__funk_rt_{routine}\n");
            assert!(asm.contains(&call), "{call}\n{asm}");
        }
        for routine in ["memcpy", "memmove", "memset"] {
            let label = format!("\n__funk_rt_{routine}:\n");
            assert_eq!(asm.matches(&label).count(), 1, "{asm}");
        }
    }

    #[test]
    fn an_i128_length_past_64_bits_saturates() {
        let asm = lowered(
            "func @f(%d: ptr, %v: i8, %n: i128) {\n^entry:\n  \
             memset nonatomic %d, %v, %n @0\n  ret @0\n}",
        )
        .unwrap();
        assert!(
            asm.contains(
                "\tmovq\t$-1, %rcx\n\ttestq\t%rax, %rax\n\tcmovnzq\t%rcx, %rdx\n\t\
                 call\t__funk_rt_memset\n"
            ),
            "{asm}"
        );
    }

    #[test]
    fn a_module_with_no_copy_carries_no_routine() {
        let asm = lowered("func @f(%a: i64) -> i64 {\n^entry:\n  ret %a @0\n}").unwrap();
        assert!(!asm.contains("__funk_rt_mem"), "{asm}");
    }

    #[test]
    fn a_copy_or_set_in_a_memory_of_16_bit_units_is_reported_at_its_pointer() {
        for op in [
            "memcpy nonatomic %d, %d, %n",
            "memmove nonatomic %d, %d, %n",
            "memset nonatomic %d, %v, %n",
        ] {
            let text = format!(
                "layout memory(1, unit(16), pointer(64), little)\n\n\
                 func @f(%d: ptr(1), %v: i16, %n: i64) {{\n^entry:\n  {op} @0\n  \
                 ret @0\n}}\n\nlocs {{\n  @0 = unknown\n}}\n"
            );
            let m = parse(&text, &Registry::core()).unwrap();
            let Err(ds) = super::super::module(&m) else {
                panic!("{op} in a memory of 16-bit units is lowered");
            };
            assert_eq!(ds.len(), 1, "{ds:?}");
            assert!(ds[0].message.starts_with("parameter %d:"), "{ds:?}");
            assert!(ds[0].message.contains("memory 1 of 16-bit units"), "{ds:?}");
        }
    }
}
