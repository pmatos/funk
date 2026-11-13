//! Conversions from floats to integers: `fptosi` and `fptoui`
//! (`decodeFloatToInt` in `lean/Fir/Core/FloatOpText.lean`, `floatToInt` in
//! `lean/Fir/Core/FloatToInt.lean`; ADR-2026-11-09-1549).
//!
//! Each takes one value of a float type `float<e,m>`, of any format, and
//! defines one value of an integer type `iN`, of any width: the number
//! truncated toward zero, read as signed by `fptosi` and as unsigned by
//! `fptoui` (the human's ruling of 2026-11-12 on #354). Truncation is what
//! the ops mean, so neither rounds and neither has an attribute:
//! `round(rne)` and every other mode do not decode. Validation has no rule
//! for these ops beyond their signature. Each is never UB, and may produce
//! poison: an integer that `iN` does not hold, an infinity or a NaN gives
//! poison.

use super::float_arith::decode_rounding;
use super::type_list;
use super::types::{float_format, int_width};
use crate::effects::Effects;
use crate::registry::{OpShape, OpSpec, OpTypes};

/// The conversions from floats to integers: `fptosi` gives a signed
/// integer, and `fptoui` an unsigned one.
pub const FLOAT_TO_INT_OPS: [&str; 2] = ["fptosi", "fptoui"];

/// `%i: i32 = fptosi %f` and `%u: i64 = fptoui %d`.
pub(super) struct FloatToInt(pub &'static str);

impl OpSpec for FloatToInt {
    fn name(&self) -> &str {
        self.0
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        decode_rounding(self.0, false, op.attrs)?;
        if let ([x], [r]) = (op.operands, op.results)
            && float_format(x).is_some()
            && int_width(r).is_some()
        {
            return Ok(OpShape::default());
        }
        Err(format!(
            "{} takes one operand of a float type and defines one value of an integer type, \
             not {} -> {}",
            self.0,
            type_list(op.operands),
            type_list(op.results)
        ))
    }

    /// May produce poison (`Core.Op.effects`).
    fn effects(&self, _op: &OpTypes<'_>) -> Effects {
        Effects {
            may_poison: true,
            ..Effects::PURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialects::core::{float_type, int_type, ptr_type};
    use crate::{Attr, Type};

    fn decode(
        name: &'static str,
        attrs: &[Attr],
        operands: &[Type],
        results: &[Type],
    ) -> Result<OpShape, String> {
        FloatToInt(name).decode(&OpTypes {
            attrs,
            operands,
            results,
        })
    }

    #[test]
    fn a_float_of_any_format_decodes_to_an_integer_of_any_width() {
        for name in FLOAT_TO_INT_OPS {
            for (e, m) in [(5, 10), (8, 7), (8, 23), (11, 52), (15, 112), (2, 1)] {
                for w in [1, 7, 8, 32, 33, 64, 128] {
                    let (f, i) = (float_type(e, m), int_type(w));
                    let got = decode(
                        name,
                        &[],
                        std::slice::from_ref(&f),
                        std::slice::from_ref(&i),
                    );
                    assert_eq!(got, Ok(OpShape::default()), "{name} float<{e},{m}> i{w}");
                }
            }
        }
    }

    #[test]
    fn every_other_pair_of_types_does_not_decode() {
        let (f32, i32) = (float_type(8, 23), int_type(32));
        for name in FLOAT_TO_INT_OPS {
            for (operands, results) in [
                (vec![f32.clone()], vec![f32.clone()]),
                (vec![i32.clone()], vec![i32.clone()]),
                (vec![i32.clone()], vec![f32.clone()]),
                (vec![ptr_type(0)], vec![i32.clone()]),
                (vec![f32.clone()], vec![ptr_type(0)]),
                (vec![f32.clone(), f32.clone()], vec![i32.clone()]),
                (vec![], vec![i32.clone()]),
                (vec![f32.clone()], vec![]),
                (vec![f32.clone()], vec![i32.clone(), i32.clone()]),
            ] {
                let e = decode(name, &[], &operands, &results).unwrap_err();
                assert!(e.starts_with(&format!("{name} takes one operand")), "{e}");
            }
        }
    }

    #[test]
    fn a_conversion_to_an_integer_takes_no_attribute() {
        let (f, i) = ([float_type(8, 23)], [int_type(32)]);
        for name in FLOAT_TO_INT_OPS {
            for bad in [
                vec![Attr::App("round".into(), vec![Attr::word("rne")])],
                vec![Attr::App("round".into(), vec![Attr::word("rtz")])],
                vec![Attr::word("rtz")],
                vec![Attr::word("nsw")],
            ] {
                let e = decode(name, &bad, &f, &i).unwrap_err();
                assert!(e.starts_with(name), "{e}");
            }
        }
    }

    #[test]
    fn a_conversion_to_an_integer_may_produce_poison() {
        let (f, i) = ([float_type(11, 52)], [int_type(64)]);
        let types = OpTypes {
            attrs: &[],
            operands: &f,
            results: &i,
        };
        for name in FLOAT_TO_INT_OPS {
            let e = FloatToInt(name).effects(&types);
            assert!(e.may_poison && !e.may_ub && !e.control, "{name}");
        }
    }
}
