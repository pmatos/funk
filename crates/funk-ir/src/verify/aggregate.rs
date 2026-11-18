//! The rule of an aggregate's layout (`Aggregate.Valid` in
//! `lean/Fir/Validation/Layout.lean`, ADR-2026-11-16-1546), checked as
//! `Aggregate.problems` in `lean/Fir/Validation/CheckLayout.lean` checks it:
//! the module has its memory, its alignment is a power of two no larger
//! than [`MemLayout::LIMIT`], its types are valid and name memories of the
//! module, each field is placed, and no two fields share a unit.
//!
//! A field is placed when its type may be a field, as the registry's
//! [`field_shape`](crate::Registry::field_shape) says, its offset is a
//! multiple of its type's alignment, that alignment is no larger than the
//! layout's, and the field ends within the layout's size. A repeated field
//! takes its count times one element's units rounded up to the element's
//! alignment, and a field that takes no units shares a unit with none. The
//! numbers are `u64`, so every one is within the spec's limit, and the
//! units are counted in `u128`, which no count times an element overflows.

use super::Diagnostic;
use crate::ir::layout::memory;
use crate::ir::{Aggregate, MemLayout, Table};
use crate::registry::{Registry, TypeCheck};

/// Checks each aggregate's layout of the table `t` against the module's
/// data layout `layout`.
pub(super) fn check(t: Table<'_>, layout: &[MemLayout], reg: &Registry, out: &mut Vec<Diagnostic>) {
    for a in t.aggregates() {
        check_one(a, layout, reg, out);
    }
}

/// The entry of memory `n` (`DataLayout.memory?`), if the module has it.
fn declared(layout: &[MemLayout], n: u64) -> Option<MemLayout> {
    u32::try_from(n).ok().and_then(|n| memory(layout, n))
}

fn check_one(a: &Aggregate, layout: &[MemLayout], reg: &Registry, out: &mut Vec<Diagnostic>) {
    let mut at = |message: String| out.push(Diagnostic::at_block(&a.name, None, message));
    if declared(layout, a.memory).is_none() {
        at(format!(
            "the layout describes memory {}, which the data layout does not declare",
            a.memory
        ));
    }
    if !u32::try_from(a.align).is_ok_and(MemLayout::valid_align) {
        at(format!(
            "the layout is aligned to {} units: an alignment is a power of two no larger than {}",
            a.align,
            MemLayout::LIMIT
        ));
    }
    if a.types().any(|t| reg.check_type(t) != TypeCheck::Valid) {
        at("a type of the layout is not valid".to_string());
    }
    let missing = a
        .types()
        .find_map(|t| reg.type_memory(t).filter(|&n| memory(layout, n).is_none()));
    if let Some(n) = missing {
        at(format!(
            "a type names memory {n}, which the data layout does not declare"
        ));
    }
    let entry = |n: u64| declared(layout, n).unwrap_or(MemLayout::DEFAULT);
    let mut spans = Vec::new();
    for f in &a.fields {
        let field = format!("the field at offset {}", f.offset);
        let Some((u, align)) = reg.field_shape(&f.ty, &entry, a.memory) else {
            at(format!(
                "{field} has a type that may not be a field: an integer or a pointer"
            ));
            continue;
        };
        let offset = u128::from(f.offset);
        let units = f.extent(u, align);
        if !offset.checked_rem(align).map_or(offset == 0, |r| r == 0) {
            at(format!(
                "{field} is not a multiple of its type's alignment, {align}"
            ));
        }
        if align > u128::from(a.align) {
            at(format!(
                "{field} has a type aligned to {align} units, more than the layout's {}",
                a.align
            ));
        }
        if offset + units > u128::from(a.size) {
            at(format!("{field} ends past the layout's size, {}", a.size));
        }
        if units > 0 {
            spans.push((offset, offset + units));
        }
    }
    spans.sort_unstable();
    if spans.windows(2).any(|w| w[1].0 < w[0].1) {
        at("two fields of the layout share a unit".to_string());
    }
}
