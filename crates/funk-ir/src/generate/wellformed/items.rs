//! The items beside functions that a well-formed module holds: items of a
//! dialect's kind, dialect sets and modules nested in it, whose items
//! include aggregates' layouts, field addresses and globals.

use super::super::{Rng, Widths, symbol, width};
use super::attr::attr;
use super::{ITEM_KINDS, Shaper, aggregate, global};
use crate::dialects::core::int_type;
use crate::ir::{Def, DialectItem, Item, NestedModule};

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
    n
}

/// Adds `fieldaddr` ops to two in three of the functions of `items`, a
/// nested module's, which may name the layouts of `items`, and `globaladdr`
/// ops to one in three, which may name the globals of `items`.
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
    }
}
