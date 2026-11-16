//! Attributes of any kind that the text writes and reads back: strings,
//! words, numbers, float literals, symbols and applied words, nested.

use super::super::{Rng, Widths, constant, name, string, symbol, width};
use crate::dialects::core::spell_float;
use crate::ir::Attr;

/// A float literal: the spelling of random bits of a format with
/// decimals, or `0x` and up to eight hexadecimal digits, any of them.
fn float_lit(rng: &mut Rng) -> Attr {
    if rng.below(2) == 0 {
        let e = 2 + rng.below(14) as u32;
        let m = 1 + rng.below(48) as u32;
        let bits = rng.next_u64() >> (63 - e - m);
        return Attr::Float(spell_float(e, m, u128::from(bits)));
    }
    let digits: String = (0..=rng.below(8))
        .map(|_| char::from_digit(rng.below(16) as u32, 16).expect("a digit below 16"))
        .collect();
    Attr::Float(format!("0x{digits}"))
}

/// An attribute of any kind, often a string or an applied word, which
/// nests below depth three.
pub(super) fn attr(rng: &mut Rng, depth: u32) -> Attr {
    match rng.below(if depth < 3 { 7 } else { 5 }) {
        0 | 1 => Attr::Str(string(rng)),
        2 => Attr::Word(name(rng, true)),
        3 if rng.below(2) == 0 => float_lit(rng),
        3 => {
            let w = width(rng, Widths::Any);
            constant(rng, w)
        }
        4 => Attr::Sym(symbol(rng)),
        5 => Attr::App(name(rng, true), Vec::new()),
        _ => {
            let args = (0..1 + rng.below(3))
                .map(|_| attr(rng, depth + 1))
                .collect();
            Attr::App(name(rng, true), args)
        }
    }
}
