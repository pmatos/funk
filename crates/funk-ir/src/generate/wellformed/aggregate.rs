//! Aggregates' layouts that the text writes and reads back, whether or not
//! validation accepts them (ADR-2026-11-16-1546): every number from 0 to
//! `2^64 - 1` decodes, and so does every core integer and pointer type of a
//! field, repeated or not.

use super::super::{Rng, Widths, symbol, width};
use crate::dialects::core::int_type;
use crate::ir::{Aggregate, Attr, Item, Type};

/// A layout of any memory, size and alignment, with up to three fields of
/// integer and pointer types at any offsets, some of them repeated.
pub(super) fn aggregate(rng: &mut Rng) -> Item {
    let number = |rng: &mut Rng| match rng.below(4) {
        0 => 0,
        1 => u64::MAX,
        _ => rng.below(65),
    };
    let mut a = Aggregate::new(symbol(rng), number(rng), number(rng), number(rng));
    for _ in 0..rng.below(4) {
        let ty = match rng.below(3) {
            0 => Type::word("ptr"),
            1 => Type::app("ptr", vec![Attr::int(i128::from(1 + rng.below(3)))]),
            _ => int_type(width(rng, Widths::Any)),
        };
        let count = rng.one_in(2).then(|| number(rng));
        a = a.field(number(rng), ty, count);
    }
    Item::Aggregate(a)
}
