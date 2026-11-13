//! Data layouts that the text writes and reads back, whether or not
//! validation accepts them (ADR-2026-11-12-1821): every number from 0 to
//! [`MemLayout::LIMIT`] decodes, and so does either byte order.

use super::super::Rng;
use crate::ir::{ByteOrder, MemLayout};

/// Declares one to three memories, in one draw of four, each with any
/// numbers that the text can write, so validation may reject the layout.
pub(super) fn add(rng: &mut Rng, layout: &mut Vec<MemLayout>) {
    if !rng.one_in(4) {
        return;
    }
    let number = |rng: &mut Rng| match rng.below(4) {
        0 => 0,
        1 => MemLayout::LIMIT,
        _ => rng.below(65) as u32,
    };
    for _ in 0..=rng.below(3) {
        layout.push(MemLayout {
            mem: number(rng),
            unit: number(rng),
            pointer: number(rng),
            order: *rng.pick(&[ByteOrder::Little, ByteOrder::Big]),
            align: rng.one_in(2).then(|| number(rng)),
            non_integral: rng.one_in(2),
        });
    }
}
