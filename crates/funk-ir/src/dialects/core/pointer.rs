//! The pointer offset: `ptradd` (`decodePtrAdd` in
//! `lean/Fir/Core/Text.lean`, `ptraddValue` in `lean/Fir/Core/Pointer.lean`;
//! #231).
//!
//! `ptradd` takes a pointer of `ptr<N>` and an integer of any width, and
//! defines a pointer of the same memory: the pointer moved by the integer,
//! read as signed, in units of the memory `N`. It has no attributes. A
//! result of another memory, an integer result, or operands of other types
//! do not decode, so validation has no rule of its own for it. It is pure:
//! it is never UB, and its result is poison only for a poison operand.

use super::type_list;
use super::types::{CoreType, core_type};
use crate::effects::Effects;
use crate::registry::{OpShape, OpSpec, OpTypes};

/// `%q: ptr = ptradd %p, %k`.
pub(super) struct PtrAdd;

impl OpSpec for PtrAdd {
    fn name(&self) -> &str {
        "ptradd"
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        if !op.attrs.is_empty() {
            return Err("ptradd takes no attributes".into());
        }
        if let ([p, k], [r]) = (op.operands, op.results)
            && let (Some(CoreType::Ptr(n)), Some(CoreType::Int(_)), Some(CoreType::Ptr(m))) =
                (core_type(p), core_type(k), core_type(r))
            && n == m
        {
            return Ok(OpShape::default());
        }
        Err(format!(
            "ptradd takes a pointer and an integer and defines a pointer of the same memory, \
             not {} -> {}",
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
    use crate::dialects::core::{MAX_MEMORY, float_type, int_type, ptr_type};
    use crate::{Attr, Type};

    fn decode(attrs: &[Attr], operands: &[Type], results: &[Type]) -> Result<OpShape, String> {
        PtrAdd.decode(&OpTypes {
            attrs,
            operands,
            results,
        })
    }

    #[test]
    fn a_pointer_and_an_integer_of_any_width_decode_in_every_memory() {
        for (n, w) in [(0, 64), (0, 1), (1, 8), (7, 128), (MAX_MEMORY, 33)] {
            let ops = [ptr_type(n), int_type(w)];
            assert_eq!(decode(&[], &ops, &[ptr_type(n)]), Ok(OpShape::default()));
        }
    }

    #[test]
    fn every_other_shape_does_not_decode() {
        let (p, p1, i64, f32) = (ptr_type(0), ptr_type(1), int_type(64), float_type(8, 23));
        for (operands, results) in [
            (vec![p.clone(), i64.clone()], vec![p1.clone()]),
            (vec![p1.clone(), i64.clone()], vec![p.clone()]),
            (vec![p.clone(), i64.clone()], vec![i64.clone()]),
            (vec![i64.clone(), p.clone()], vec![p.clone()]),
            (vec![p.clone(), p.clone()], vec![p.clone()]),
            (vec![p.clone(), f32.clone()], vec![p.clone()]),
            (vec![p.clone()], vec![p.clone()]),
            (vec![p.clone(), i64.clone(), i64.clone()], vec![p.clone()]),
            (vec![p.clone(), i64.clone()], vec![]),
            (vec![p.clone(), i64.clone()], vec![p.clone(), p.clone()]),
        ] {
            let e = decode(&[], &operands, &results).unwrap_err();
            assert!(
                e.starts_with("ptradd takes a pointer and an integer"),
                "{e}"
            );
        }
    }

    #[test]
    fn ptradd_takes_no_attributes() {
        for a in [Attr::word("inbounds"), Attr::word("nuw"), Attr::int(1)] {
            let e = decode(&[a], &[ptr_type(0), int_type(64)], &[ptr_type(0)]).unwrap_err();
            assert_eq!(e, "ptradd takes no attributes");
        }
    }

    #[test]
    fn ptradd_is_pure() {
        let op = OpTypes {
            attrs: &[],
            operands: &[ptr_type(0), int_type(64)],
            results: &[ptr_type(0)],
        };
        assert_eq!(PtrAdd.effects(&op), Effects::PURE);
    }
}
