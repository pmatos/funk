//! Constants: `const` (`Op.decode` in `lean/Fir/Core/Text.lean`).
//!
//! `const` has one attribute, its value, no operands and one `iN` result. An
//! `i1` constant is written `true` or `false`. Every other constant is
//! written as its bits read as a two's-complement signed integer, in decimal,
//! so each bit pattern has one spelling: `const 1` and `const -1` at `i1` do
//! not decode, and neither does a value that does not fit its type.

use super::types::int_width;
use crate::Attr;
use crate::registry::{OpShape, OpSpec, OpTypes};

/// `%c: iN = const v`.
pub(super) struct Const;

impl OpSpec for Const {
    fn name(&self) -> &str {
        "const"
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        if !op.operands.is_empty() {
            return Err("const takes no operands".into());
        }
        let [result] = op.results else {
            return Err("const defines one value".into());
        };
        let Some(width) = int_width(result) else {
            return Err(format!(
                "const defines an integer, not a value of type {result}"
            ));
        };
        let [value] = op.attrs else {
            return Err("const has one attribute, its value".into());
        };
        match (width, value) {
            (1, Attr::Word(w)) if w == "true" || w == "false" => Ok(OpShape::default()),
            (1, Attr::Int(_)) => Err("an i1 constant is written true or false".into()),
            (_, Attr::Int(v)) if v.fits_signed(width) => Ok(OpShape::default()),
            (_, Attr::Int(v)) => Err(format!("the constant {v} does not fit {result}")),
            (_, Attr::Word(w)) if w == "true" || w == "false" => Err(format!(
                "{w} is an i1 constant, and this const is of type {result}"
            )),
            (_, other) => Err(format!("the value of a const is an integer, not {other}")),
        }
    }
}
