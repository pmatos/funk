//! A function's frame under spill-everything register allocation
//! (ADR-2026-10-30-1230).
//!
//! Every value a function defines, parameters first, then each block's
//! arguments and each op's results in order, has an 8-byte slot of its own
//! below `%rbp`: the first at `-8(%rbp)`, the next at `-16(%rbp)`. An op
//! loads its operands from their slots into scratch registers, computes, and
//! stores each result into its slot. No value stays in a register from one
//! op to the next.
//!
//! Below the values' slots, a frame holds what the result convention needs
//! (ADR-2026-11-03-0109): a slot for the address of the function's own
//! result area when its results go in memory, a slot for the address that
//! it passes to a call whose results go in memory, and at its bottom the
//! area for those calls, as large as the largest that one of them needs.
//!
//! A frame of a page or more is probed a page at a time as the prologue
//! makes room for it, so the stack grows one page after another and never
//! jumps over a guard region into memory below it.

use std::collections::HashMap;

use funk_ir::Func;

use crate::abi::results::{Area, Layout};
use crate::asm::{Asm, Mem, Reg};
use crate::lower::callee;

/// The size of a page: the stack grows, and a frame is probed, a page at a
/// time.
pub const PAGE: i32 = 4096;

/// The slots of a function's values, what its results and calls need, and
/// the frame's size.
#[derive(Debug)]
pub struct Frame<'f> {
    slots: HashMap<&'f str, Mem>,
    results: Option<Mem>,
    area: Option<Area>,
    size: i32,
}

impl<'f> Frame<'f> {
    /// The frame of `f`, or why it cannot have one: its slots must lie
    /// within 2 GiB of `%rbp`, the reach of a 32-bit displacement.
    pub fn new(f: &'f Func) -> Result<Frame<'f>, String> {
        let defs = f.params.iter().chain(
            f.body
                .blocks
                .iter()
                .flat_map(|b| b.params.iter().chain(b.ops.iter().flat_map(|o| &o.results))),
        );
        let mut slots = HashMap::new();
        for d in defs {
            let n = slots.len() + 1;
            let disp = displacement(n).ok_or_else(too_big)?;
            slots.entry(d.name.as_str()).or_insert(Mem { disp });
        }
        let mut count = slots.len();
        let mut next = || {
            count += 1;
            displacement(count)
                .map(|disp| Mem { disp })
                .ok_or_else(too_big)
        };
        let returns = Layout::of_types(&f.results)?;
        let results = if returns.in_memory() {
            Some(next()?)
        } else {
            None
        };
        let mut most = 0;
        for op in f.body.blocks.iter().flat_map(|b| &b.ops) {
            if callee(op).is_some() {
                let l = Layout::of_types(op.results.iter().map(|d| &d.ty))?;
                most = most.max(l.area());
            }
        }
        let address = if most > 0 { Some(next()?) } else { None };
        let size = size_for(count)
            .and_then(|s| s.checked_add(most))
            .ok_or_else(too_big)?;
        let area = address.map(|address| Area {
            address,
            base: Mem { disp: -size },
        });
        Ok(Frame {
            slots,
            results,
            area,
            size,
        })
    }

    /// The slot of the value named `name`.
    pub fn slot(&self, name: &str) -> Option<Mem> {
        self.slots.get(name).copied()
    }

    /// The slot that holds the address of the function's own result area,
    /// which it receives first, when its results go in memory.
    pub fn results_address(&self) -> Option<Mem> {
        self.results
    }

    /// The result area for the function's calls whose results go in memory,
    /// if it makes any.
    pub fn result_area(&self) -> Option<Area> {
        self.area
    }

    /// The frame's size in bytes below `%rbp`: a multiple of 16.
    pub fn size(&self) -> i32 {
        self.size
    }
}

fn too_big() -> String {
    "the function defines more values than a frame of 2 GiB holds".into()
}

/// The displacement of the `n`-th slot, from 1: `-8 * n`.
pub fn displacement(n: usize) -> Option<i32> {
    i32::try_from(n).ok()?.checked_mul(-8)
}

/// The size of a frame of `n` slots: `8 * n`, rounded up to 16 so that
/// `%rsp` stays 16-byte aligned, as calls need.
pub fn size_for(n: usize) -> Option<i32> {
    let bytes = i32::try_from(n).ok()?.checked_mul(8)?;
    bytes.checked_add(15).map(|b| b & !15)
}

/// The standard prologue: saves `%rbp`, points it at the frame, and makes
/// room for `size` bytes of slots.
///
/// A frame of a page or more is probed: the prologue moves `%rsp` down a
/// page at a time and touches each page as it goes, then makes room for the
/// rest, which is less than a page. A smaller frame is one `subq`, at most
/// 4080 bytes. Either way the next write, a call's return address or a
/// stack argument after its padding, is at most a page below the last
/// access, so the stack grows in order, and a frame too large for its stack
/// faults on the guard page below it rather than writing past it
/// (ADR-2026-11-02-1102). The probe loop counts in `%r11`, which carries no
/// argument, so the parameters are still in their registers after it.
pub fn prologue(asm: &mut Asm, size: i32) {
    asm.ins("pushq", format_args!("%rbp"));
    asm.ins("movq", format_args!("%rsp, %rbp"));
    let (pages, rest) = if size >= PAGE {
        (size / PAGE, size % PAGE)
    } else {
        (0, size)
    };
    if pages > 0 {
        let count = Reg::R11.at(32);
        asm.ins("movl", format_args!("${pages}, {count}"));
        asm.label("1");
        asm.ins("subq", format_args!("${PAGE}, %rsp"));
        asm.ins("orq", format_args!("$0, (%rsp)"));
        asm.ins("decl", format_args!("{count}"));
        asm.ins("jnz", format_args!("1b"));
    }
    if rest > 0 {
        asm.ins("subq", format_args!("${rest}, %rsp"));
    }
}

/// The epilogue: drops the frame, restores `%rbp` and returns.
pub fn epilogue(asm: &mut Asm) {
    asm.ins0("leave");
    asm.ins0("ret");
}

#[cfg(test)]
mod tests {
    use funk_ir::{Registry, parse};

    use super::*;

    #[test]
    fn every_value_has_its_own_slot_in_order() {
        let text = "func @f(%a: i32, %b: i32) -> i32 {\n^entry:\n  %c: i32 = add %a, %b @0\n  ret %c @0\n}\n\nlocs {\n  @0 = unknown\n}\n";
        let m = parse(text, &Registry::core()).unwrap();
        let f = m.funcs().next().unwrap();
        let frame = Frame::new(f).unwrap();
        assert_eq!(frame.slot("a"), Some(Mem { disp: -8 }));
        assert_eq!(frame.slot("b"), Some(Mem { disp: -16 }));
        assert_eq!(frame.slot("c"), Some(Mem { disp: -24 }));
        assert_eq!(frame.slot("d"), None);
        assert_eq!(frame.size(), 32);
    }

    /// After the values: the slot for the function's own result area's
    /// address, the slot for the address it passes, and at the bottom the
    /// largest area that one of its calls needs (ADR-2026-11-03-0109).
    #[test]
    fn a_frame_holds_what_results_in_memory_need() {
        let text = "func @three() -> i8, i8, i8 {\n^entry:\n  %c: i8 = const 1 @0\n  ret %c, %c, %c @0\n}\n\n\
                    func @five() -> i8, i8, i8, i8, i8 {\n^entry:\n  \
                    %a: i8, %b: i8, %c: i8 = call @three @0\n  ret %a, %b, %c, %a, %b @0\n}\n\n\
                    func @f() -> i8, i8 {\n^entry:\n  %a: i8, %b: i8, %c: i8 = call @three @0\n  \
                    %d: i8, %e: i8, %f: i8, %g: i8, %h: i8 = call @five @0\n  ret %a, %h @0\n}\n\n\
                    locs {\n  @0 = unknown\n}\n";
        let m = parse(text, &Registry::core()).unwrap();
        let frames: Vec<Frame> = m.funcs().map(|f| Frame::new(f).unwrap()).collect();
        assert_eq!(frames[0].results_address(), Some(Mem { disp: -16 }));
        assert_eq!(frames[0].result_area(), None);
        assert_eq!(frames[0].size(), 16);
        assert_eq!(frames[1].results_address(), Some(Mem { disp: -32 }));
        let area = Area {
            address: Mem { disp: -40 },
            base: Mem { disp: -80 },
        };
        assert_eq!(frames[1].result_area(), Some(area));
        assert_eq!(frames[1].size(), 48 + 32);
        assert_eq!(frames[2].results_address(), None);
        let area = Area {
            address: Mem { disp: -72 },
            base: Mem { disp: -128 },
        };
        assert_eq!(frames[2].result_area(), Some(area));
        assert_eq!(frames[2].size(), 80 + 48);
        assert_eq!(frames[2].slot("h"), Some(Mem { disp: -64 }));
    }

    fn prologue_of(size: i32) -> String {
        let mut asm = Asm::new();
        prologue(&mut asm, size);
        asm.finish()
    }

    #[test]
    fn a_frame_smaller_than_a_page_is_not_probed() {
        let start = "\tpushq\t%rbp\n\tmovq\t%rsp, %rbp\n";
        assert_eq!(prologue_of(0), start);
        assert_eq!(prologue_of(16), format!("{start}\tsubq\t$16, %rsp\n"));
        assert_eq!(prologue_of(4080), format!("{start}\tsubq\t$4080, %rsp\n"));
    }

    /// A frame of exactly a page is probed too: a call after a bare
    /// `subq $4096` would push its return address 4104 bytes below the last
    /// access, past a one-page guard region.
    #[test]
    fn a_frame_of_one_page_is_probed() {
        let probe = "\tpushq\t%rbp\n\tmovq\t%rsp, %rbp\n\tmovl\t$1, %r11d\n1:\n\tsubq\t$4096, %rsp\n\torq\t$0, (%rsp)\n\tdecl\t%r11d\n\tjnz\t1b\n";
        assert_eq!(prologue_of(PAGE), probe);
        assert_eq!(
            prologue_of(PAGE + 16),
            format!("{probe}\tsubq\t$16, %rsp\n")
        );
    }

    #[test]
    fn a_larger_frame_is_probed_a_page_at_a_time() {
        let probe = "\tpushq\t%rbp\n\tmovq\t%rsp, %rbp\n\tmovl\t$2, %r11d\n1:\n\tsubq\t$4096, %rsp\n\torq\t$0, (%rsp)\n\tdecl\t%r11d\n\tjnz\t1b\n";
        assert_eq!(prologue_of(8192), probe);
        assert_eq!(
            prologue_of(8192 + 48),
            format!("{probe}\tsubq\t$48, %rsp\n")
        );
        let big = prologue_of(size_for(1 << 27).unwrap());
        assert!(big.contains("\tmovl\t$262144, %r11d\n"), "{big}");
    }

    #[test]
    fn frames_stay_aligned_and_within_reach() {
        assert_eq!(size_for(0), Some(0));
        assert_eq!(size_for(1), Some(16));
        assert_eq!(size_for(2), Some(16));
        assert_eq!(size_for(3), Some(32));
        assert_eq!(displacement(1), Some(-8));
        assert_eq!(size_for(1 << 28), None);
        assert_eq!(displacement(1 << 28), Some(i32::MIN));
        assert_eq!(displacement((1 << 28) + 1), None);
    }
}
