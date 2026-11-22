//! Pointers as integers: `ptr_expose` and `ptr_from_int`
//! (`dialects/core/ptr_int.rs` in `funk-ir`;
//! `docs/decisions/x86-64-backend-lowering-memory.md#pointers-as-integers`).
//!
//! A pointer is its 64-bit address, so both ops are moves: `ptr_expose`
//! copies the pointer's slot into its `i64` result's, and `ptr_from_int`
//! copies the `i64`'s slot into its pointer result's. The data layout asks
//! that the integer be as wide as the memory's pointers, and the backend
//! realises only memories of 64-bit pointers, so the integer is an `i64`;
//! a pointer of any other memory is reported where it is defined.
//!
//! The addresses that native code gives its allocations are one address
//! policy of the spec for each memory: aligned, from 1, below `2^64 - 1`,
//! and no two live allocations overlapping. So the integer that
//! `ptr_expose` gives is an address that the spec may give, and a pointer
//! rebuilt from it, in any memory, reaches what an allocation that the
//! spec's resolver may pick holds: a live, exposed allocation of that memory
//! whose addresses, its end included, hold it. An address that none holds
//! gives a pointer through which every access is UB, so whatever native
//! code then reaches refines the spec.

use super::{Lower, bitcast};

/// `%a: i64 = ptr_expose %p` and `%q: ptr<N> = ptr_from_int %a`: the
/// operand's slot, copied to the result's, as a bit cast copies it.
pub(super) fn lowering(name: &str) -> Option<Lower> {
    match name {
        "ptr_expose" | "ptr_from_int" => Some(bitcast::copy),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use funk_ir::{Registry, parse};

    fn lowered(text: &str) -> Result<String, Vec<funk_ir::Diagnostic>> {
        let text = format!("{text}\n\nlocs {{\n  @0 = unknown\n}}\n");
        let m = parse(&text, &Registry::core()).unwrap();
        super::super::module(&m).map(|l| l.text)
    }

    #[test]
    fn each_op_copies_its_operand_s_slot_to_its_result_s() {
        let asm = lowered(
            "func @f(%x: i32) -> i32, i64 {\n^entry:\n  %p: ptr = alloca stack i32 @0\n  \
             store nonatomic %x, %p @0\n  %a: i64 = ptr_expose %p @0\n  \
             %q: ptr = ptr_from_int %a @0\n  %v: i32 = load nonatomic %q @0\n  \
             ret %v, %a @0\n}",
        )
        .unwrap();
        for op in ["%a: i64 = ptr_expose %p @0", "%q: ptr = ptr_from_int %a @0"] {
            let at = asm.find(op).unwrap_or_else(|| panic!("{op}\n{asm}"));
            let code: Vec<&str> = asm[at..].lines().skip(1).take(2).collect();
            assert!(
                code[0].starts_with("\tmovq\t") && code[0].ends_with(", %rax"),
                "{asm}"
            );
            assert!(code[1].starts_with("\tmovq\t%rax, "), "{asm}");
        }
    }

    #[test]
    fn a_pointer_of_a_memory_of_32_bit_pointers_is_reported_where_it_is_defined() {
        let ds = lowered(
            "layout memory(1, unit(8), pointer(32), little)\n\n\
             func @f(%p: ptr(1)) -> i32 {\n^entry:\n  %a: i32 = ptr_expose %p @0\n  \
             %q: ptr(1) = ptr_from_int %a @0\n  %b: i32 = ptr_expose %q @0\n  ret %b @0\n}",
        )
        .unwrap_err();
        assert_eq!(ds.len(), 2, "{ds:?}");
        assert!(
            ds.iter()
                .all(|d| d.message.contains("memory 1 of 8-bit units and 32-bit")),
            "{ds:?}"
        );
    }
}
