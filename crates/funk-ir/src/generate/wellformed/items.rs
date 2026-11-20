//! The items beside functions that a well-formed module holds: items of a
//! dialect's kind, dialect sets and modules nested in it, whose items
//! include aggregates' layouts, field addresses and globals.

use super::super::{Rng, Widths, symbol, width};
use super::attr::attr;
use super::{ITEM_KINDS, Shaper, aggregate, field_addr, global};
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
    field_addr::add_to_items(rng, &mut n.items);
    if depth > 1 && rng.one_in(3) {
        n.items.push(Item::Module(nested(rng, depth - 1)));
    }
    n
}
