//! Where a funk function's results go (ADR-2026-11-03-0109): as System V
//! returns a structure with one member per result, each aligned to 8 bytes,
//! or to 16 for an `i128`.
//!
//! A result of at most 64 bits takes one eightbyte, an `i128` two, its low
//! half first. Results of one or two eightbytes come back in registers, as
//! System V classifies them: each INTEGER eightbyte in the next of `%rax`
//! and `%rdx`, and each SSE eightbyte, an `f32` or an `f64`, in the next of
//! `%xmm0` and `%xmm1` (ADR-2026-11-11-1140). More go in a result area that
//! the caller provides in its frame:
//! it passes the area's address as the call's first argument, and the
//! callee writes every result there and returns the address in `%rax`.
//! An `i1` result is 0 or 1 in all of its eightbyte; every other result is
//! in the low bits of its eightbyte, as a slot holds it. The caller stores
//! each eightbyte in a slot as it comes (ADR-2026-11-02-1021).
//!
//! `ret`, `call` and the entry wrapper all lay out and move their results
//! here, so the convention has one definition.

use funk_ir::Type;

use crate::abi::RESULT_REG;
use crate::asm::{Asm, Mem, Reg};
use crate::width::{self, Class, Ext};

/// The registers that carry the first two eightbytes of results, in order.
pub const RESULT_REGS: [Reg; 2] = [RESULT_REG, Reg::Rdx];

/// Where one eightbyte of a list of results goes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Place {
    /// In this register.
    Reg(Reg),
    /// In the SSE register `%xmmN`.
    Xmm(u8),
    /// At this offset in the result area.
    Area(i32),
}

/// What a caller's frame holds for its calls whose results go in memory.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Area {
    /// The slot that holds the area's address while a call passes it.
    pub address: Mem,
    /// The area's lowest byte, 16-byte aligned.
    pub base: Mem,
}

/// Where each result of a function or a call goes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    /// One place per eightbyte, in order: a result of at most 64 bits has
    /// one, an `i128` two, its low half first.
    places: Vec<Place>,
    /// The bytes of the result area, a multiple of 16; 0 when every result
    /// comes back in registers.
    area: i32,
}

impl Layout {
    /// The layout of integer results of the widths `widths`, each one that
    /// the backend lowers: at most 64, or 128, as [`Layout::of_classes`]
    /// lays them out.
    pub fn new(widths: &[u32]) -> Result<Layout, String> {
        let classes: Vec<Class> = widths
            .iter()
            .map(|&w| if w > 64 { Class::Pair } else { Class::Int })
            .collect();
        Layout::of_classes(&classes)
    }

    /// The layout of results of the classes `classes`. Fails when the area
    /// would not fit in the 2 GiB that a displacement reaches.
    pub fn of_classes(classes: &[Class]) -> Result<Layout, String> {
        let words: usize = classes.iter().map(|c| c.words()).sum();
        if words <= RESULT_REGS.len() {
            let (mut int, mut sse) = (0, 0);
            let mut places = Vec::with_capacity(words);
            for &c in classes {
                for _ in 0..c.words() {
                    if c == Class::Sse {
                        places.push(Place::Xmm(sse));
                        sse += 1;
                    } else {
                        places.push(Place::Reg(RESULT_REGS[int]));
                        int += 1;
                    }
                }
            }
            return Ok(Layout { places, area: 0 });
        }
        let mut places = Vec::with_capacity(words);
        let mut end = 0u64;
        for &c in classes {
            let n = c.words() as u64;
            let at = end.next_multiple_of(8 * n);
            for k in 0..n {
                places.push(Place::Area(fits(at + 8 * k)?));
            }
            end = at + 8 * n;
        }
        let area = fits(end.next_multiple_of(16))?;
        Ok(Layout { places, area })
    }

    /// The layout of results of the types `types`. A type that the backend
    /// does not lower counts as one eightbyte: lowering reports it where its
    /// value is defined, so no code is built with this layout.
    pub fn of_types<'t>(types: impl IntoIterator<Item = &'t Type>) -> Result<Layout, String> {
        let classes: Vec<Class> = types.into_iter().map(width::class).collect();
        Layout::of_classes(&classes)
    }

    /// Where each eightbyte of the results goes, in order.
    pub fn places(&self) -> &[Place] {
        &self.places
    }

    /// The bytes of the result area that a caller provides, a multiple of
    /// 16, or 0 when the results come back in registers.
    pub fn area(&self) -> i32 {
        self.area
    }

    /// Whether the results go in a result area.
    pub fn in_memory(&self) -> bool {
        self.area > 0
    }

    /// The words that a call passes before its own arguments: the area's
    /// address when the results go in memory, and nothing otherwise.
    pub fn hidden_arguments(&self) -> usize {
        usize::from(self.in_memory())
    }

    /// What `ret` does before the epilogue: puts each eightbyte of the
    /// results, read from its slot in `from` with its value's width, where
    /// it goes. An `i1` goes as 0 or 1 in all 64 bits. `address` is the slot
    /// in which the function keeps the address of its result area, which it
    /// returns in `%rax`.
    pub fn give(
        &self,
        asm: &mut Asm,
        address: Option<Mem>,
        from: &[(Mem, u32)],
    ) -> Result<(), String> {
        self.count(from.len())?;
        let base = RESULT_REG;
        if self.in_memory() {
            let address = address.ok_or("the function has no slot for its result area")?;
            asm.ins("movq", format_args!("{address}, {}", base.q()));
        }
        for (&place, &(slot, w)) in self.places.iter().zip(from) {
            let reg = match place {
                Place::Reg(reg) => reg,
                Place::Xmm(n) => {
                    asm.ins("movq", format_args!("{slot}, %xmm{n}"));
                    continue;
                }
                Place::Area(_) => Reg::Rcx,
            };
            asm.ins("movq", format_args!("{slot}, {}", reg.q()));
            if w == 1 {
                width::extend(asm, Ext::Zero, 1, reg);
            }
            if let Place::Area(at) = place {
                asm.ins("movq", format_args!("{}, {at}({})", reg.q(), base.q()));
            }
        }
        Ok(())
    }

    /// What a caller does before the call when the results go in memory:
    /// it stores the address of its frame's result area in the slot that
    /// the call passes first (ADR-2026-11-02-1428).
    pub fn pass(&self, asm: &mut Asm, area: Area) {
        let rax = RESULT_REG.q();
        asm.ins("leaq", format_args!("{}, {rax}", area.base));
        asm.ins("movq", format_args!("{rax}, {}", area.address));
    }

    /// What a caller does after the call: stores each eightbyte of the
    /// results, as it comes, in its slot in `into`. `area` is the caller's
    /// result area, which the call was given when the results go in memory.
    pub fn receive(&self, asm: &mut Asm, area: Option<Area>, into: &[Mem]) -> Result<(), String> {
        self.count(into.len())?;
        let mut moves = Vec::with_capacity(into.len());
        for (&place, &slot) in self.places.iter().zip(into) {
            let from = match place {
                Place::Reg(reg) => reg.q().to_string(),
                Place::Xmm(n) => format!("%xmm{n}"),
                Place::Area(at) => {
                    let area = area.ok_or("the caller has no result area")?;
                    let disp = area.base.disp.checked_add(at);
                    let disp = disp.ok_or("the result area is out of the reach of %rbp")?;
                    Mem { disp }.to_string()
                }
            };
            moves.push((place, from, slot));
        }
        let rax = RESULT_REG.q();
        for (place, from, slot) in moves {
            if let Place::Area(_) = place {
                asm.ins("movq", format_args!("{from}, {rax}"));
                asm.ins("movq", format_args!("{rax}, {slot}"));
            } else {
                asm.ins("movq", format_args!("{from}, {slot}"));
            }
        }
        Ok(())
    }

    fn count(&self, n: usize) -> Result<(), String> {
        if n == self.places.len() {
            Ok(())
        } else {
            Err(format!(
                "the results take {} eightbytes, and {n} slots were given",
                self.places.len()
            ))
        }
    }
}

fn fits(bytes: u64) -> Result<i32, String> {
    i32::try_from(bytes)
        .map_err(|_| "the results take more than a result area of 2 GiB holds".into())
}

#[cfg(test)]
#[path = "results_tests.rs"]
mod tests;
