//! The rule of a global (`Global.Valid` in `lean/Fir/Validation/Global.lean`,
//! ADR-2026-11-09-1546), checked as `Global.problems` in
//! `lean/Fir/Validation/CheckGlobal.lean` checks it: the module has its
//! memory, its alignment is a power of two no larger than
//! [`MemLayout::LIMIT`], each unit of its initializer fits its memory's
//! unit, each address names a global of its own table, and the initializer
//! takes no more units than its size. An address takes the units of one
//! pointer of its global's memory in the memory of the global that holds
//! it. The numbers are `u64`, so every one is within the spec's limit.

use super::Diagnostic;
use crate::ir::layout::memory;
use crate::ir::{Global, InitPiece, MemLayout, Nat, Table};

/// Checks each global of the table `t` against the module's data layout
/// `layout`, as an item of `t`.
pub(super) fn check(t: Table<'_>, layout: &[MemLayout], out: &mut Vec<Diagnostic>) {
    let globals: Vec<&Global> = t.globals().collect();
    for g in &globals {
        check_one(g, &globals, layout, out);
    }
}

/// The entry of memory `n` (`DataLayout.memory?`), if the module has it.
fn declared(layout: &[MemLayout], n: u64) -> Option<MemLayout> {
    u32::try_from(n).ok().and_then(|n| memory(layout, n))
}

/// The units of `w` bits in a memory of `unit`-bit units
/// (`MemLayout.bitsUnits`), 0 for a unit of no bits.
fn bits_units(w: u32, unit: u32) -> u128 {
    if unit == 0 {
        0
    } else {
        u128::from(w.div_ceil(unit))
    }
}

fn check_one(g: &Global, globals: &[&Global], layout: &[MemLayout], out: &mut Vec<Diagnostic>) {
    let mut at = |message: String| out.push(Diagnostic::at_block(&g.name, None, message));
    if declared(layout, g.memory).is_none() {
        at(format!(
            "the global lives in memory {}, which the data layout does not declare",
            g.memory
        ));
    }
    if !u32::try_from(g.align).is_ok_and(MemLayout::valid_align) {
        at(format!(
            "the global is aligned to {} units: an alignment is a power of two no larger than {}",
            g.align,
            MemLayout::LIMIT
        ));
    }
    let entry = |n: u64| declared(layout, n).unwrap_or(MemLayout::DEFAULT);
    let unit = entry(g.memory).unit;
    let named = |s: &str| globals.iter().find(|h| h.name == s);
    let mut units: u128 = 0;
    for p in &g.init {
        match p {
            InitPiece::Units(us) => {
                let wide = us
                    .iter()
                    .find(|u| Nat::from_decimal(u.as_str()).bit_len() > u64::from(unit));
                if let Some(u) = wide {
                    at(format!(
                        "the unit {u} of the initializer does not fit in {unit} bits"
                    ));
                }
                units = units.saturating_add(us.len() as u128);
            }
            InitPiece::Zeros(k) => units = units.saturating_add(u128::from(*k)),
            InitPiece::Addr(s, _) => match named(s) {
                Some(h) => units = units.saturating_add(bits_units(entry(h.memory).pointer, unit)),
                None => at(format!(
                    "the initializer's address of @{s} names no global of its table"
                )),
            },
        }
    }
    if units > u128::from(g.size) {
        at(format!(
            "the initializer takes {units} units, more than the global's size, {}",
            g.size
        ));
    }
}
