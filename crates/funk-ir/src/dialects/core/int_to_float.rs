//! Conversions from integers to floats: `sitofp` and `uitofp`
//! (`decodeIntToFloat` in `lean/Fir/Core/FloatOpText.lean`, `intToFloat` in
//! `lean/Fir/Core/FloatOfInt.lean`; ADR-2026-11-09-1549).
//!
//! Each takes one value of an integer type `iN`, of any width, and defines
//! one value of a float type `float<e,m>`, of any format: the integer that
//! the operand holds, read as signed by `sitofp` and as unsigned by
//! `uitofp`, rounded to nearest even. Each rounds, so it has one attribute,
//! its rounding mode `round(MODE)`, as the float arithmetic does
//! (ADR-2026-11-11-1801). Every mode decodes, and validation accepts only
//! `round(rne)`, the one mode M1 has (the human's ruling of 2026-11-15 on
//! #229). Each is pure: it is never UB, its result is never a NaN, and it
//! gives poison only for a poison operand.

use super::rounding::{check_rounding, decode_rounding};
use super::type_list;
use super::types::{float_format, int_width};
use crate::effects::Effects;
use crate::registry::{OpContext, OpShape, OpSpec, OpTypes};

/// The conversions from integers to floats: `sitofp` reads its operand as
/// signed, and `uitofp` as unsigned.
pub const INT_TO_FLOAT_OPS: [&str; 2] = ["sitofp", "uitofp"];

/// `%f: f32 = sitofp round(rne) %i` and `%f: f64 = uitofp round(rne) %i`.
pub(super) struct IntToFloat(pub &'static str);

impl OpSpec for IntToFloat {
    fn name(&self) -> &str {
        self.0
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        decode_rounding(self.0, true, op.attrs)?;
        if let ([x], [r]) = (op.operands, op.results)
            && int_width(x).is_some()
            && float_format(r).is_some()
        {
            return Ok(OpShape::default());
        }
        Err(format!(
            "{} takes one operand of an integer type and defines one value of a float type, \
             not {} -> {}",
            self.0,
            type_list(op.operands),
            type_list(op.results)
        ))
    }

    /// The mode `rne` (`Op.Valid`).
    fn check(&self, _cx: &OpContext<'_>, op: &OpTypes<'_>) -> Result<(), String> {
        check_rounding(self.0, op.attrs)
    }

    /// Pure (`Core.Op.effects`).
    fn effects(&self, _op: &OpTypes<'_>) -> Effects {
        Effects::PURE
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialects::core::{float_type, int_type, ptr_type};
    use crate::{Attr, Type};

    fn rne() -> Attr {
        Attr::App("round".into(), vec![Attr::word("rne")])
    }

    fn decode(
        name: &'static str,
        attrs: &[Attr],
        operands: &[Type],
        results: &[Type],
    ) -> Result<OpShape, String> {
        IntToFloat(name).decode(&OpTypes {
            attrs,
            operands,
            results,
        })
    }

    #[test]
    fn an_integer_of_any_width_decodes_to_a_float_of_any_format() {
        for name in INT_TO_FLOAT_OPS {
            for w in [1, 7, 8, 32, 33, 64, 128] {
                for (e, m) in [(5, 10), (8, 7), (8, 23), (11, 52), (15, 112), (2, 1)] {
                    let (i, f) = (int_type(w), float_type(e, m));
                    let got = decode(
                        name,
                        &[rne()],
                        std::slice::from_ref(&i),
                        std::slice::from_ref(&f),
                    );
                    assert_eq!(got, Ok(OpShape::default()), "{name} i{w} float<{e},{m}>");
                }
            }
        }
    }

    #[test]
    fn every_other_pair_of_types_does_not_decode() {
        let (f32, i32) = (float_type(8, 23), int_type(32));
        for name in INT_TO_FLOAT_OPS {
            for (operands, results) in [
                (vec![f32.clone()], vec![f32.clone()]),
                (vec![i32.clone()], vec![i32.clone()]),
                (vec![f32.clone()], vec![i32.clone()]),
                (vec![ptr_type(0)], vec![f32.clone()]),
                (vec![i32.clone(), i32.clone()], vec![f32.clone()]),
                (vec![], vec![f32.clone()]),
                (vec![i32.clone()], vec![]),
                (vec![i32.clone()], vec![f32.clone(), f32.clone()]),
            ] {
                let e = decode(name, &[rne()], &operands, &results).unwrap_err();
                assert!(e.starts_with(&format!("{name} takes one operand")), "{e}");
            }
        }
    }

    #[test]
    fn a_conversion_needs_a_rounding_mode() {
        let (i, f) = ([int_type(32)], [float_type(8, 23)]);
        for name in INT_TO_FLOAT_OPS {
            for bad in [
                vec![],
                vec![Attr::App("round".into(), vec![Attr::word("up")])],
                vec![rne(), rne()],
                vec![Attr::word("nsw")],
            ] {
                let e = decode(name, &bad, &i, &f).unwrap_err();
                assert!(e.starts_with(name) && e.contains("round("), "{e}");
            }
        }
    }

    #[test]
    fn every_mode_decodes_and_validation_accepts_only_rne() {
        for name in INT_TO_FLOAT_OPS {
            super::super::rounding::assert_every_mode_decodes_and_only_rne_validates(
                &IntToFloat(name),
                &[int_type(32)],
                &[float_type(8, 23)],
            );
        }
    }
}
