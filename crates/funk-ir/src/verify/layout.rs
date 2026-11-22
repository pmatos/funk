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
//! block defines; and then of `Func.attrTypes`: the types that its ops
//! carry in their attributes, op by op. Last, a function an op of which
//! writes values into the units of a memory whose units are not as wide,
//! such as a `memset` of an `i16` into memory 0, gets one diagnostic, which
//! names the first such memory (`unitsProblem`). Then a function an op of
//! which turns the pointers of a memory into integers, or back, of a width
//! that is not its pointers', or of a memory that the layout marks
//! non-integral, such as a `ptr_expose` of a `ptr` into an `i32`, gets one
//! diagnostic, which names the first such memory (`addrsProblem`).

use std::collections::{HashMap, HashSet};

use super::Diagnostic;
use crate::ir::Part;
use crate::ir::layout::memory;
use crate::ir::{ByteOrder, Func, MemLayout, Table, Type};
use crate::registry::{OpSpec, OpTypes, Registry};

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
        if let Some(a) = e.align.filter(|&a| !MemLayout::valid_align(a)) {
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
/// `t` names, gives units as wide as the values that its functions' ops
/// write into them, and pointers as wide as the integers that its
/// functions' ops turn them into, in integral memories
/// (`SymbolTable.MemoriesIn`).
pub(super) fn check_memories(
    t: Table<'_>,
    layout: &[MemLayout],
    reg: &Registry,
    out: &mut Vec<Diagnostic>,
) {
    let missing = |ty: &Type| reg.type_memory(ty).filter(|&n| memory(layout, n).is_none());
    let mut asking = Vec::new();
    for f in t.funcs() {
        let mut first = f.types().find_map(missing);
        let mut asks = false;
        for o in attr_ops(f) {
            let Some(spec) = reg.op(&o.name) else {
                continue;
            };
            asks |= spec.asks_unit_widths();
            if first.is_none() {
                first = spec.attr_types(&o.attrs).iter().find_map(missing);
            }
        }
        if let Some(n) = first {
            out.push(problem(&f.name, n));
        }
        if asks {
            asking.push(f);
        }
    }
    for i in t.dialect_items() {
        if let Some(n) = i.types().find_map(missing) {
            out.push(problem(&i.name, n));
        }
    }
    for e in t.externs() {
        if let Some(n) = e.types().find_map(missing) {
            out.push(problem(&e.name, n));
        }
    }
    let entry = |n| memory(layout, n).unwrap_or(MemLayout::DEFAULT);
    for f in asking {
        let unit_ops =
            attr_ops(f).filter(|o| reg.op(&o.name).is_some_and(|s| s.asks_unit_widths()));
        let bad = |(n, w): (u32, u32)| entry(n).unit != w;
        if let Some((n, w)) = first_width(f, unit_ops, reg, |s, op| s.unit_widths(op), bad) {
            let unit = entry(n).unit;
            out.push(Diagnostic::at_block(
                &f.name,
                None,
                format!(
                    "an op writes values of {w} bits into memory {n}, whose units have {unit} bits"
                ),
            ));
        }
    }
    for f in t.funcs() {
        let mut addr_ops = all_ops(f)
            .filter(|o| reg.op(&o.name).is_some_and(|s| s.asks_addr_widths()))
            .peekable();
        if addr_ops.peek().is_none() {
            continue;
        }
        let bad = |(n, w): (u32, u32)| entry(n).pointer != w || entry(n).non_integral;
        if let Some((n, w)) = first_width(f, addr_ops, reg, |s, op| s.addr_widths(op), bad) {
            let message = if entry(n).non_integral {
                format!(
                    "an op turns pointers of memory {n} into integers or back, but the memory is non-integral"
                )
            } else {
                let pointer = entry(n).pointer;
                format!(
                    "an op turns pointers of memory {n} into integers of {w} bits or back, but its pointers have {pointer} bits"
                )
            };
            out.push(Diagnostic::at_block(&f.name, None, message));
        }
    }
}

/// The first pair of a memory and a width that `widths` gives for one of the
/// ops `ops` of `f` and that is `bad`: `unitsProblem` over `Func.unitWidths`
/// and `addrsProblem` over `Func.addrWidths`. An op whose operands are not
/// defined, or which does not decode, asks for none: the rules of ops
/// report it. Only the ops `ops`, whose specs ask, have their operands
/// typed.
fn first_width<'f>(
    f: &'f Func,
    mut ops: impl Iterator<Item = &'f crate::ir::Op>,
    reg: &Registry,
    widths: fn(&dyn OpSpec, &OpTypes<'_>) -> Vec<(u32, u32)>,
    bad: impl Fn((u32, u32)) -> bool,
) -> Option<(u32, u32)> {
    let mut types: HashMap<&str, &Type> = HashMap::new();
    let defs = f.body.parts().flat_map(|part| match part {
        Part::Block(b) => b
            .params
            .iter()
            .chain(b.ops.iter().flat_map(|o| &o.results))
            .collect(),
        _ => Vec::new(),
    });
    for d in f.params.iter().chain(defs) {
        types.entry(d.name.as_str()).or_insert(&d.ty);
    }
    ops.find_map(|o| {
        let spec = reg.op(&o.name)?;
        let operands: Vec<Type> = o
            .operands
            .iter()
            .map(|x| types.get(x.as_str()).map(|t| (*t).clone()))
            .collect::<Option<_>>()?;
        let results: Vec<Type> = o.results.iter().map(|d| d.ty.clone()).collect();
        let op = OpTypes {
            attrs: &o.attrs,
            operands: &operands,
            results: &results,
        };
        spec.decode(&op).ok()?;
        widths(spec, &op).into_iter().find(|&q| bad(q))
    })
}

/// The ops of `f`'s blocks, at any depth.
fn all_ops(f: &Func) -> impl Iterator<Item = &crate::ir::Op> {
    f.body
        .parts()
        .filter_map(|part| match part {
            Part::Block(b) => Some(&b.ops),
            _ => None,
        })
        .flatten()
}

/// The ops of `f`'s blocks that have attributes: the only ones that may
/// carry a type or ask a unit width.
fn attr_ops(f: &Func) -> impl Iterator<Item = &crate::ir::Op> {
    all_ops(f).filter(|o| !o.attrs.is_empty())
}

fn problem(sym: &str, n: u32) -> Diagnostic {
    Diagnostic::at_block(
        sym,
        None,
        format!("a type names memory {n}, which the data layout does not declare"),
    )
}
