//! The rules of a module's data layout (ADR-2026-11-12-1821):
//! `DataLayout.Valid` and `Module.MemoriesDeclared`, in
//! `lean/Fir/Validation/Layout.lean`, checked as
//! `lean/Fir/Validation/CheckLayout.lean` checks them.
//!
//! A valid layout declares each memory once, and each entry gives a unit and
//! a pointer of 1 to [`MemLayout::LIMIT`] bits, the byte order `little`,
//! which is the only one M1 admits, and an alignment, if any, that is a power
//! of two no larger than the limit. Each pointer type of each symbol table,
//! the module's own and each nested module's, names a memory that the
//! module's one layout declares: memory 0 always, and another when the
//! layout has an entry for it. A function, or an item of a dialect's kind,
//! whose types name a memory that the layout does not declare gets one
//! diagnostic, which names the first such memory in the order of
//! `Func.types`: its results, its parameters, then the values that each
//! block defines.

use std::collections::HashSet;

use super::Diagnostic;
use crate::ir::layout::memory;
use crate::ir::{ByteOrder, MemLayout, Table, Type};
use crate::registry::Registry;

/// The rules of the layout's entries (`DataLayout.problems`): each entry's
/// problems in order, then each memory declared more than once.
pub(super) fn check_entries(layout: &[MemLayout], out: &mut Vec<Diagnostic>) {
    let limit = MemLayout::LIMIT;
    for e in layout {
        let at = format!("data layout: memory {}", e.mem);
        if e.mem > limit {
            out.push(Diagnostic::module(format!("{at} is above {limit}")));
        }
        if !(1..=limit).contains(&e.unit) {
            out.push(Diagnostic::module(format!(
                "{at} has a unit of {} bits: a unit has 1 to {limit} bits",
                e.unit
            )));
        }
        if !(1..=limit).contains(&e.pointer) {
            out.push(Diagnostic::module(format!(
                "{at} has pointers of {} bits: a pointer has 1 to {limit} bits",
                e.pointer
            )));
        }
        if e.order != ByteOrder::Little {
            out.push(Diagnostic::module(format!(
                "{at} is big-endian: M1 admits only little-endian memories"
            )));
        }
        if let Some(a) = e.align.filter(|&a| !a.is_power_of_two() || a > limit) {
            out.push(Diagnostic::module(format!(
                "{at} aligns its pointers to {a} units: an alignment is a power of two no larger than {limit}"
            )));
        }
    }
    let mut seen = HashSet::new();
    for e in layout {
        if !seen.insert(e.mem) {
            out.push(Diagnostic::module(format!(
                "data layout: memory {} is declared more than once",
                e.mem
            )));
        }
    }
}

/// The rule that `layout` declares each memory that a type of the table
/// `t` names (`SymbolTable.MemoriesIn`).
pub(super) fn check_memories(
    t: Table<'_>,
    layout: &[MemLayout],
    reg: &Registry,
    out: &mut Vec<Diagnostic>,
) {
    let missing = |ty: &Type| reg.type_memory(ty).filter(|&n| memory(layout, n).is_none());
    for f in t.funcs() {
        if let Some(n) = f.types().find_map(missing) {
            out.push(problem(&f.name, n));
        }
    }
    for i in t.dialect_items() {
        if let Some(n) = i.types().find_map(missing) {
            out.push(problem(&i.name, n));
        }
    }
}

fn problem(sym: &str, n: u32) -> Diagnostic {
    Diagnostic::at_block(
        sym,
        None,
        format!("a type names memory {n}, which the data layout does not declare"),
    )
}
