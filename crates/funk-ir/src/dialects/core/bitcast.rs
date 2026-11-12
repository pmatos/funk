//! Bit casts: `bitcast` (`decodeBitcast` in
//! `lean/Fir/Core/FloatOpText.lean`, `bitcastValue` in
//! `lean/Fir/Core/FloatBitcast.lean`; ADR-2026-11-09-1549).
//!
//! `bitcast` takes one value and defines one value of the same width: from
//! `float<e,m>` to `iN`, or from `iN` to `float<e,m>`, with `N = 1 + e + m`.
//! The types say which way it goes, and it has no attributes. A pair of
//! types whose widths differ, or two floats or two integers, does not
//! decode, so validation has no rule of its own for it. It is pure: the
//! result has the operand's bits, a NaN's sign and payload included, and
//! is poison only for a poison operand.

use super::type_list;
use super::types::{float_format, int_width};
use crate::Type;
use crate::effects::Effects;
use crate::registry::{OpShape, OpSpec, OpTypes};

/// Whether `float` is `float<e,m>` and `int` is `iN` with `N = 1 + e + m`.
fn same_width(float: &Type, int: &Type) -> bool {
    match (float_format(float), int_width(int)) {
        (Some((e, m)), Some(n)) => u64::from(e) + u64::from(m) + 1 == u64::from(n),
        _ => false,
    }
}

/// `%b: i32 = bitcast %f` and `%f: f32 = bitcast %b`.
pub(super) struct Bitcast;

impl OpSpec for Bitcast {
    fn name(&self) -> &str {
        "bitcast"
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        if !op.attrs.is_empty() {
            return Err("bitcast takes no attributes".into());
        }
        if let ([x], [r]) = (op.operands, op.results)
            && (same_width(x, r) || same_width(r, x))
        {
            return Ok(OpShape::default());
        }
        Err(format!(
            "bitcast takes one operand and defines one value, a float type float<e,m> and an \
             integer type of its width 1 + e + m in either order, not {} -> {}",
            type_list(op.operands),
            type_list(op.results)
        ))
    }

    /// Pure (`Core.Op.effects`).
    fn effects(&self, _op: &OpTypes<'_>) -> Effects {
        Effects::PURE
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Attr;
    use crate::dialects::core::{float_type, int_type, ptr_type};

    fn decode(attrs: &[Attr], operands: &[Type], results: &[Type]) -> Result<OpShape, String> {
        Bitcast.decode(&OpTypes {
            attrs,
            operands,
            results,
        })
    }

    #[test]
    fn a_float_and_an_integer_of_its_width_decode_both_ways() {
        for (e, m) in [
            (5, 10),
            (8, 7),
            (8, 23),
            (11, 52),
            (15, 112),
            (2, 1),
            (1, 0),
        ] {
            let (f, i) = (float_type(e, m), int_type(1 + e + m));
            let (f, i) = (std::slice::from_ref(&f), std::slice::from_ref(&i));
            assert_eq!(decode(&[], f, i), Ok(OpShape::default()));
            assert_eq!(decode(&[], i, f), Ok(OpShape::default()));
        }
    }

    #[test]
    fn every_other_pair_of_types_does_not_decode() {
        let (f32, f64, i32, i64) = (
            float_type(8, 23),
            float_type(11, 52),
            int_type(32),
            int_type(64),
        );
        for (operands, results) in [
            (vec![f32.clone()], vec![i64.clone()]),
            (vec![i64.clone()], vec![f32.clone()]),
            (vec![f64.clone()], vec![i32.clone()]),
            (vec![i32.clone()], vec![i32.clone()]),
            (vec![f32.clone()], vec![f32.clone()]),
            (vec![float_type(5, 10)], vec![float_type(8, 7)]),
            (vec![ptr_type(0)], vec![i64.clone()]),
            (vec![f32.clone(), f32.clone()], vec![i32.clone()]),
            (vec![], vec![i32.clone()]),
            (vec![f32.clone()], vec![]),
            (vec![f32.clone()], vec![i32.clone(), i32.clone()]),
        ] {
            let e = decode(&[], &operands, &results).unwrap_err();
            assert!(e.starts_with("bitcast takes one operand"), "{e}");
        }
    }

    #[test]
    fn bitcast_takes_no_attributes() {
        let round = Attr::App("round".into(), vec![Attr::word("rne")]);
        for a in [round, Attr::word("nuw"), Attr::int(1)] {
            let e = decode(&[a], &[float_type(8, 23)], &[int_type(32)]).unwrap_err();
            assert_eq!(e, "bitcast takes no attributes");
        }
    }
}
