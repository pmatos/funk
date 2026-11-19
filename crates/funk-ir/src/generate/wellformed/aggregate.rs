//! Aggregates' layouts that the text writes and reads back, whether or not
//! validation accepts them (ADR-2026-11-16-1546): every number from 0 to
//! `2^64 - 1` decodes, and so does every core integer, float and pointer
//! type of a field, repeated or not.

use super::super::{Rng, Widths, symbol, width};
use crate::dialects::core::{FLOAT_ALIASES, MAX_WIDTH, float_type, int_type};
use crate::ir::{Aggregate, Attr, Type};

/// A layout of any memory, size and alignment, with up to three fields of
/// integer, float and pointer types at any offsets, some of them repeated.
pub(super) fn aggregate(rng: &mut Rng) -> Aggregate {
    let number = |rng: &mut Rng| match rng.below(4) {
        0 => 0,
        1 => u64::MAX,
        _ => rng.below(65),
    };
    let mut a = Aggregate::new(symbol(rng), number(rng), number(rng), number(rng));
    for _ in 0..rng.below(4) {
        let ty = match rng.below(5) {
            0 => Type::word("ptr"),
            1 => Type::app("ptr", vec![Attr::int(i128::from(1 + rng.below(3)))]),
            2 | 3 => float(rng),
            _ => int_type(width(rng, Widths::Any)),
        };
        let count = rng.one_in(2).then(|| number(rng));
        a = a.field(number(rng), ty, count);
    }
    a
}

/// A float type that decodes: a named format, or `float(e, m)` of any
/// numbers of bits, those that validation rejects among them, such as
/// `float(0, 0)`, and C's `long double`, `float(15, 64)`.
fn float(rng: &mut Rng) -> Type {
    let (e, m) = match rng.below(4) {
        0 => {
            let (_, e, m) = *rng.pick(&FLOAT_ALIASES);
            (e, m)
        }
        1 => (15, 64),
        2 => (rng.below(3) as u32, rng.below(3) as u32),
        _ => {
            let e = rng.below(20) as u32;
            (e, rng.below(u64::from(MAX_WIDTH - e)) as u32)
        }
    };
    float_type(e, m)
}
