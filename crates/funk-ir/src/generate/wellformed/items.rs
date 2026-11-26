//! The items beside functions that a well-formed module holds: items of a
//! dialect's kind, dialect sets and modules nested in it, whose items
//! include aggregates' layouts, field addresses and globals.

use super::super::{Rng, Widths, symbol, width};
use super::attr::attr;
use super::{ITEM_KINDS, Shaper, aggregate, global};
use crate::dialects::core::int_type;
use crate::ir::{Attr, Def, DialectItem, Extern, Item, NestedModule, trim_attrs};

/// An item of a kind from [`ITEM_KINDS`], with up to two parameters, two
/// results of core types and three attributes.
pub(super) fn dialect_item(rng: &mut Rng) -> Item {
    let mut i = DialectItem::new(*rng.pick(&ITEM_KINDS), symbol(rng));
    let mut taken = Vec::new();
    for _ in 0..rng.below(3) {
        let t = int_type(width(rng, Widths::Any));
        i.params.push(Def::new(Shaper::fresh(rng, &mut taken), t));
    }
    i.results = (0..rng.below(3))
        .map(|_| int_type(width(rng, Widths::Any)))
        .collect();
    i.attrs = (0..rng.below(4)).map(|_| attr(rng, 0)).collect();
    Item::Dialect(i)
}

/// An external declaration with up to three parameters and two results of
/// core types, each with up to two attributes that may or may not be the
/// core's markers, ending in `...` or not (ADR-2026-11-09-1547).
pub(super) fn extern_decl(rng: &mut Rng) -> Item {
    let mut e = Extern::new(symbol(rng));
    let mut taken = Vec::new();
    let marks = |rng: &mut Rng| -> Vec<Attr> {
        (0..rng.below(3))
            .map(|_| match rng.below(3) {
                0 => Attr::word("sext"),
                1 => Attr::word("zext"),
                _ => attr(rng, 0),
            })
            .collect()
    };
    let mut param_attrs = Vec::new();
    for _ in 0..rng.below(4) {
        let t = int_type(width(rng, Widths::Any));
        e.params.push(Def::new(Shaper::fresh(rng, &mut taken), t));
        param_attrs.push(marks(rng));
    }
    let mut result_attrs = Vec::new();
    for _ in 0..rng.below(3) {
        e.results.push(int_type(width(rng, Widths::Any)));
        result_attrs.push(marks(rng));
    }
    e.param_attrs = trim_attrs(param_attrs);
    e.result_attrs = trim_attrs(result_attrs);
    e.variadic = rng.one_in(2);
    Item::Extern(e)
}

/// Names one to three dialects, drawn with repeats, in one draw of four.
pub(super) fn add_dialects(rng: &mut Rng, dialects: &mut Vec<String>) {
    if rng.one_in(4) {
        for _ in 0..=rng.below(3) {
            dialects.push(rng.pick(&["toy", "gpu", "x_1"]).to_string());
        }
    }
}

/// A nested module at most `depth` deep: the functions of a valid module,
/// then, in one draw of three, a module nested in it.
pub(super) fn nested(rng: &mut Rng, depth: u32) -> NestedModule {
    let mut n = NestedModule::new(symbol(rng));
    add_dialects(rng, &mut n.dialects);
    n.items = super::super::module(rng).items;
    if rng.one_in(3) {
        n.items.push(dialect_item(rng));
    }
    if rng.one_in(3) {
        n.items.push(Item::Aggregate(aggregate::aggregate(rng)));
    }
    if rng.one_in(3) {
        n.items.push(global::global(rng));
    }
    add_addresses(rng, &mut n.items);
    if depth > 1 && rng.one_in(3) {
        n.items.push(Item::Module(nested(rng, depth - 1)));
    }
    if rng.one_in(3) {
        n.items.push(extern_decl(rng));
    }
    n
}

/// Adds `fieldaddr` ops to two in three of the functions of `items`, a
/// nested module's, which may name the layouts of `items`, `globaladdr`
/// ops to one in three, which may name the globals of `items`, and
/// `funcaddr` ops to one in three, which may name the functions of
/// `items`.
fn add_addresses(rng: &mut Rng, items: &mut [Item]) {
    let symbols: Vec<String> = items
        .iter()
        .filter_map(Item::as_func)
        .map(|f| f.name.clone())
        .collect();
    let layouts: Vec<String> = items
        .iter()
        .filter_map(Item::as_aggregate)
        .map(|a| a.name.clone())
        .collect();
    let globals: Vec<String> = items
        .iter()
        .filter_map(Item::as_global)
        .map(|g| g.name.clone())
        .collect();
    for item in items {
        let Item::Func(f) = item else { continue };
        if f.body.blocks.is_empty() {
            continue;
        }
        let mut shaper = Shaper::new(f, &symbols, &[], false);
        if !rng.one_in(3) {
            shaper.add_field_addrs(rng, f, &layouts);
        }
        if rng.one_in(3) {
            shaper.add_global_addrs(rng, f, &globals);
        }
        if rng.one_in(3) {
            shaper.add_func_addrs(rng, f);
        }
    }
}
