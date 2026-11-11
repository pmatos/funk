//! Constants: `const` and `poison` (`Op.decode` in
//! `lean/Fir/Core/Text.lean`).
//!
//! `const` has one attribute, its value, no operands and one `iN` or float
//! result. An `i1` constant is written `true` or `false`. Every other
//! integer constant is written as its bits read as a two's-complement
//! signed integer, in decimal, so each bit pattern has one spelling:
//! `const 1` and `const -1` at `i1` do not decode, and neither does a value
//! that does not fit its type. A float constant is the one float literal
//! of its bits (ADR-2026-11-11-1438, `float_text`).
//!
//! `poison` has no attributes, no operands and one `iN` result, the poison
//! of its type (ADR-2026-11-03-1615).

use super::types::{CoreType, core_type, int_width};
use crate::Attr;
use crate::effects::Effects;
use crate::registry::{OpShape, OpSpec, OpTypes};

/// `%c: iN = const v`, and `%c: f32 = const v` for every float type.
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
        let [value] = op.attrs else {
            return Err("const has one attribute, its value".into());
        };
        let width = match core_type(result) {
            Some(CoreType::Int(w)) => w,
            Some(CoreType::Float { e, m }) => return float_constant(e, m, value, result),
            _ => {
                return Err(format!(
                    "const defines an integer or a float, not a value of type {result}"
                ));
            }
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

    /// Pure (`Core.Op.effects`).
    fn effects(&self, _op: &OpTypes<'_>) -> Effects {
        Effects::PURE
    }
}

/// Checks that `value` is a constant of `float<e,m>`, the type `result`:
/// the one float literal of some bits of it.
fn float_constant(e: u32, m: u32, value: &Attr, result: &crate::Type) -> Result<OpShape, String> {
    match value {
        Attr::Float(s) => super::float_text::float_constant(e, m, s)
            .map(|_| OpShape::default())
            .map_err(|why| format!("{why}: it is no constant of {result}")),
        other => Err(format!(
            "the value of a float const is a float literal, such as 1.0 or 0x7fc00000, not {other}"
        )),
    }
}

/// `%p: iN = poison`.
pub(super) struct Poison;

impl OpSpec for Poison {
    fn name(&self) -> &str {
        "poison"
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        if !op.attrs.is_empty() {
            return Err("poison takes no attributes".into());
        }
        if !op.operands.is_empty() {
            return Err("poison takes no operands".into());
        }
        let [result] = op.results else {
            return Err("poison defines one value".into());
        };
        if int_width(result).is_none() {
            return Err(format!(
                "poison defines an integer, not a value of type {result}"
            ));
        }
        Ok(OpShape::default())
    }

    /// May produce poison: it gives poison from no operand
    /// (`Core.Op.effects`).
    fn effects(&self, _op: &OpTypes<'_>) -> Effects {
        Effects {
            may_poison: true,
            ..Effects::PURE
        }
    }
}
