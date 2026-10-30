//! A function's frame under spill-everything register allocation
//! (ADR-2026-10-30-1230).
//!
//! Every value a function defines, parameters first, then each block's
//! arguments and each op's results in order, has an 8-byte slot of its own
//! below `%rbp`: the first at `-8(%rbp)`, the next at `-16(%rbp)`. An op
//! loads its operands from their slots into scratch registers, computes, and
//! stores each result into its slot. No value stays in a register from one
//! op to the next.

use std::collections::HashMap;

use funk_ir::Func;

use crate::asm::{Asm, Mem};

/// The slots of a function's values, and the frame's size.
#[derive(Debug)]
pub struct Frame<'f> {
    slots: HashMap<&'f str, Mem>,
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
        let size = size_for(slots.len()).ok_or_else(too_big)?;
        Ok(Frame { slots, size })
    }

    /// The slot of the value named `name`.
    pub fn slot(&self, name: &str) -> Option<Mem> {
        self.slots.get(name).copied()
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
pub fn prologue(asm: &mut Asm, size: i32) {
    asm.ins("pushq", format_args!("%rbp"));
    asm.ins("movq", format_args!("%rsp, %rbp"));
    if size > 0 {
        asm.ins("subq", format_args!("${size}, %rsp"));
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
