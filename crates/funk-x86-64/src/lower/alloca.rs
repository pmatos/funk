//! Stack allocation: `alloca` (`dialects/core/alloca.rs` in `funk-ir`;
//! `docs/decisions/x86-64-backend-lowering-memory.md#stack-allocation`).
//!
//! Each run of an `alloca` makes a new allocation that lives until its call
//! returns, so one inside a loop has a new one on every pass. The backend
//! moves `%rsp` down at run time: below the frame, by the allocation's
//! bytes rounded up to 16, then down to its alignment, at least 16 so that
//! calls keep their aligned `%rsp`. It touches each page it passes, a page
//! at a time from where `%rsp` was, so the stack still grows in order and a
//! run that outgrows its stack faults on the guard page
//! (`docs/decisions/x86-64-backend.md#stack-probes`). The epilogue's `leave`
//! frees every allocation of the call. The allocation's bytes are not
//! cleared: they hold poison, which any bits refine.
//!
//! An `alloca` that runs at most once per call, in a block on no cycle of
//! the function's branches, adds the most it can move `%rsp` to the
//! function's stack need; one on a cycle makes the need unbounded, as a
//! recursion does (`stack.rs`,
//! `docs/decisions/x86-64-backend-executable.md#the-figure`).
//!
//! The allocation holds `count` values of its type in the memory of its
//! result: `ceil(N / 8)` bytes for an `iN`, and the bytes of `M`'s pointer
//! width for a `ptr<M>`. Without `align(A)` it is aligned as the spec says
//! (`MemLayout.intAlign` and `Ty.defaultAlign` in the Lean): the natural
//! alignment of those bytes, the least power of two at least as many, or,
//! for a pointer in its own memory, that memory's pointer alignment. A size
//! past 64 bits saturates: no stack holds it, so the run reports that it
//! cannot reserve its stack, or runs out of it.

use std::collections::HashSet;

use funk_ir::dialects::core::{CoreType, allocation, core_type};
use funk_ir::ir::layout::memory;
use funk_ir::{Func, Op};

use super::memory::realised;
use super::stack::components;
use super::{Cx, Lower, Unlowered};
use crate::asm::Reg;
use crate::frame::PAGE;

pub(super) fn lowering(name: &str) -> Option<Lower> {
    match name {
        "alloca" => Some(alloca),
        _ => None,
    }
}

/// The alignment that `%rsp` keeps at every call.
const STACK_ALIGN: u64 = 16;

/// The labels of the blocks of `f` that lie on a cycle of its branches, so
/// that their ops may run more than once per call; empty when `f` has no
/// `alloca`, the one op that asks.
pub fn looping(f: &Func) -> HashSet<&str> {
    let blocks = &f.body.blocks;
    if !blocks
        .iter()
        .flat_map(|b| &b.ops)
        .any(|o| o.name == "alloca")
    {
        return HashSet::new();
    }
    let index: std::collections::HashMap<&str, usize> = blocks
        .iter()
        .enumerate()
        .rev()
        .map(|(i, b)| (b.label.as_str(), i))
        .collect();
    let edges: Vec<Vec<usize>> = blocks
        .iter()
        .map(|b| {
            b.ops
                .iter()
                .flat_map(|o| &o.succs)
                .filter_map(|s| index.get(s.label.as_str()).copied())
                .collect()
        })
        .collect();
    let mut out = HashSet::new();
    for members in components(&edges) {
        if members.len() > 1 || edges[members[0]].contains(&members[0]) {
            out.extend(members.into_iter().map(|i| blocks[i].label.as_str()));
        }
    }
    out
}

/// The bytes and the alignment of the allocation of the `alloca` `op`,
/// whose result is a pointer of memory `n`.
fn sized(cx: &Cx<'_>, op: &Op, n: u32) -> Result<(u64, u64), Unlowered> {
    let a = allocation(&op.attrs).ok_or("alloca's attributes do not decode")?;
    let own = realised(cx.layout, n)?;
    let (bytes, natural) = match a.element {
        CoreType::Int(w) => (u64::from(w.div_ceil(8)), None),
        CoreType::Ptr(m) => {
            let e = memory(cx.layout, m).ok_or_else(|| format!("no memory {m}"))?;
            let bytes = u64::from(e.pointer.div_ceil(own.unit));
            (bytes, (m == n).then(|| e.alignment()))
        }
        CoreType::Float { .. } => return Err("alloca allocates no float".into()),
    };
    // A count past 64 bits has no stack to fit in, as one just below has
    // none, so it saturates.
    let count = a
        .count
        .map_or(Some(1), |c| c.as_str().parse::<u64>().ok())
        .unwrap_or(u64::MAX);
    let align = a.align.map_or_else(
        || natural.unwrap_or_else(|| bytes.next_power_of_two()),
        u64::from,
    );
    Ok((bytes.saturating_mul(count), align))
}

/// `%p: ptr<N> = alloca stack T [count] [align(A)]`.
fn alloca(cx: &mut Cx<'_>, op: &Op) -> Result<(), Unlowered> {
    let ([], [p]) = (op.operands.as_slice(), op.results.as_slice()) else {
        return Err("alloca takes no operand and defines a pointer".into());
    };
    cx.width(&p.name)?;
    let Some(CoreType::Ptr(n)) = core_type(&p.ty) else {
        return Err("alloca defines a pointer".into());
    };
    let (bytes, align) = sized(cx, op, n)?;
    let align = align.max(STACK_ALIGN);
    let mask = i32::try_from(align)
        .ok()
        .and_then(i32::checked_neg)
        .ok_or_else(|| format!("alloca aligns to {align} bytes, past a 32-bit mask"))?;
    let total = bytes.saturating_add(STACK_ALIGN - 1) & !(STACK_ALIGN - 1);
    if cx.looping.contains(cx.block) {
        cx.stack.unbounded = true;
    } else {
        let most = total.saturating_add(align - STACK_ALIGN);
        cx.stack.allocas = cx.stack.allocas.saturating_add(most);
    }
    let (wrapped, probe, done) = (cx.local_label(), cx.local_label(), cx.local_label());
    let asm = &mut cx.asm;
    asm.ins("movq", format_args!("%rsp, %rax"));
    // `as` reads a 64-bit immediate as signed.
    asm.ins("movabsq", format_args!("${}, %rcx", total as i64));
    asm.ins("subq", format_args!("%rcx, %rax"));
    // Past the bottom of the address space, aim at 0: the probes below
    // reach the guard page first.
    asm.ins("jae", format_args!("{wrapped}"));
    asm.ins("xorl", format_args!("%eax, %eax"));
    asm.label(&wrapped);
    asm.ins("andq", format_args!("${mask}, %rax"));
    asm.label(&probe);
    asm.ins("orq", format_args!("$0, (%rsp)"));
    asm.ins("leaq", format_args!("-{PAGE}(%rsp), %rcx"));
    asm.ins("cmpq", format_args!("%rax, %rcx"));
    asm.ins("jb", format_args!("{done}"));
    asm.ins("movq", format_args!("%rcx, %rsp"));
    asm.ins("jmp", format_args!("{probe}"));
    asm.label(&done);
    asm.ins("movq", format_args!("%rax, %rsp"));
    asm.ins("orq", format_args!("$0, (%rsp)"));
    cx.store(&p.name, Reg::Rax)
}

#[cfg(test)]
mod tests {
    use funk_ir::{Registry, parse};

    use super::*;
    use crate::lower::Need;

    fn module(funcs: &str) -> (String, Vec<Need>) {
        let text = format!("{funcs}\n\nlocs {{\n  @0 = unknown\n}}\n");
        let m = parse(&text, &Registry::core()).unwrap();
        let l = super::super::module(&m).unwrap();
        (l.text, l.needs)
    }

    #[test]
    fn only_blocks_on_a_cycle_loop() {
        let text = "func @f(%n: i1) {\n^entry:\n  %p: ptr = alloca stack i8 @0\n  br ^head @0\n\
                    ^head:\n  cond_br %n, ^body, ^exit @0\n^body:\n  br ^head @0\n\
                    ^exit:\n  ret @0\n}\n\nfunc @g() {\n^entry:\n  ret @0\n}\n\n\
                    locs {\n  @0 = unknown\n}\n";
        let m = parse(text, &Registry::core()).unwrap();
        let fs: Vec<&Func> = m.funcs().collect();
        let mut got: Vec<&str> = looping(fs[0]).into_iter().collect();
        got.sort_unstable();
        assert_eq!(got, ["body", "head"]);
        assert!(looping(fs[1]).is_empty());
    }

    #[test]
    fn an_allocation_moves_rsp_by_its_rounded_bytes_and_alignment() {
        let (asm, needs) = module(
            "func @f() -> ptr {\n^entry:\n  %p: ptr = alloca stack i32 3 @0\n  \
             %q: ptr = alloca stack i8 align(64) @0\n  ret %q @0\n}",
        );
        assert!(asm.contains("\tmovabsq\t$16, %rcx\n"), "{asm}");
        assert!(asm.contains("\tandq\t$-16, %rax\n"), "{asm}");
        assert!(asm.contains("\tandq\t$-64, %rax\n"), "{asm}");
        assert!(
            asm.contains("\tmovq\t%rax, %rsp\n\torq\t$0, (%rsp)\n\tmovq\t%rax, -8(%rbp)\n"),
            "{asm}"
        );
        // Two slots, 16 + 16 for the frame's return address and `%rbp`,
        // 16 for the first, and 16 + 48 of padding for the second.
        assert_eq!(needs[0].bytes, 16 + 16 + 16 + 16 + 48);
        assert!(!needs[0].unbounded);
    }

    #[test]
    fn an_allocation_in_a_loop_makes_the_function_unbounded() {
        let (_, needs) = module(
            "func @f(%n: i1) {\n^entry:\n  br ^body @0\n^body:\n  \
             %p: ptr = alloca stack i64 @0\n  cond_br %n, ^body, ^exit @0\n\
             ^exit:\n  ret @0\n}\n\nfunc @g(%n: i1) {\n^entry:\n  call @f %n @0\n  ret @0\n}",
        );
        assert!(needs[0].unbounded && needs[1].unbounded, "{needs:?}");
    }

    #[test]
    fn a_pointer_takes_the_pointer_bytes_and_alignment_of_its_memory() {
        let text = "layout memory(1, unit(8), pointer(64), little, align(32))\n\n\
                    func @f() -> ptr(1) {\n^entry:\n  %p: ptr(1) = alloca stack ptr(1) @0\n  \
                    ret %p @0\n}\n\nfunc @g() -> ptr {\n^entry:\n  \
                    %p: ptr = alloca stack ptr(1) 3 @0\n  ret %p @0\n}\n\n\
                    locs {\n  @0 = unknown\n}\n";
        let m = parse(text, &Registry::core()).unwrap();
        let l = super::super::module(&m).unwrap();
        assert!(l.text.contains("\tandq\t$-32, %rax\n"), "{}", l.text);
        // 24 bytes round to 32, at the natural alignment 8, raised to 16.
        assert!(l.text.contains("\tmovabsq\t$32, %rcx\n"), "{}", l.text);
        assert_eq!(l.needs[0].bytes, 16 + 16 + 16 + 16);
        assert_eq!(l.needs[1].bytes, 16 + 16 + 32);
    }

    #[test]
    fn a_count_past_64_bits_saturates() {
        let (asm, needs) = module(
            "func @f() -> ptr {\n^entry:\n  \
             %p: ptr = alloca stack i64 36893488147419103232 @0\n  ret %p @0\n}",
        );
        assert!(asm.contains("\tmovabsq\t$-16, %rcx\n"), "{asm}");
        assert_eq!(needs[0].bytes, u64::MAX);
    }
}
