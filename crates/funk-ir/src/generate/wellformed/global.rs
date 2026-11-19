//! Globals that the text writes and reads back, whether or not validation
//! accepts them (ADR-2026-11-09-1546): every number but a unit's from 0 to
//! `2^64 - 1`, any natural number as a unit, `constant` and `export` or not,
//! and the address of the global itself or of any other symbol.

use super::super::{Rng, symbol};
use crate::ir::{Global, InitPiece, Int, Item, Linkage, Nat};

/// A global of any memory, size and alignment, with up to three pieces.
pub(super) fn global(rng: &mut Rng) -> Item {
    let number = |rng: &mut Rng| match rng.below(4) {
        0 => 0,
        1 => u64::MAX,
        _ => rng.below(65),
    };
    let name = symbol(rng);
    let mut g = Global::new(name.clone(), number(rng), number(rng), number(rng));
    g.constant = rng.one_in(2);
    if rng.one_in(2) {
        g.linkage = Linkage::Exported;
    }
    for _ in 0..rng.below(4) {
        let piece = match rng.below(3) {
            0 => InitPiece::Units(
                (0..rng.below(4))
                    .map(|_| match rng.below(4) {
                        0 => Int::from_nat(false, &Nat::pow2(64 + rng.below(80))),
                        _ => Int::from(i128::from(rng.below(256))),
                    })
                    .collect(),
            ),
            1 => InitPiece::Zeros(number(rng)),
            _ => {
                let target = if rng.one_in(2) {
                    name.clone()
                } else {
                    symbol(rng)
                };
                InitPiece::Addr(target, number(rng))
            }
        };
        g.init.push(piece);
    }
    Item::Global(g)
}
