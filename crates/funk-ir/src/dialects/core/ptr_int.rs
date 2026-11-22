//! Pointers as integers: `ptr_expose` and `ptr_from_int` (`decodePtrExpose`
//! and `decodePtrFromInt` in `lean/Fir/Core/PtrIntText.lean`, their rules in
//! `lean/Fir/Core/PtrInt.lean`, and `Op.addrWidths` in
//! `lean/Fir/Core/Validation.lean`; #232, ADR-2026-11-09-1542).
//!
//! `%a: iW = ptr_expose %p` exposes the pointer `%p` of `ptr<N>` and defines
//! its address, and `%q: ptr<N> = ptr_from_int %a` turns the integer `%a`
//! back into a pointer of `ptr<N>`. Neither has attributes, and an integer
//! of any width decodes: the data layout asks that `W` be the width of
//! memory `N`'s pointers and that memory `N` be integral
//! ([`OpSpec::addr_widths`]), which the verifier checks with the rules of
//! the layout.
//!
//! Each reads memory `N` and allocates in it: exposing counts as allocating
//! (the human's ruling of 2026-11-20 on #232, question B), and so does
//! turning an integer back into a pointer (the human's ruling of 2026-11-21).
//! `ptr_expose` may be UB, on a poison pointer and when no address may be
//! given; `ptr_from_int` never is. On defined operands neither gives poison.

use super::type_list;
use super::types::{CoreType, core_type};
use crate::effects::{Effects, MemSet as Memories};
use crate::registry::{OpShape, OpSpec, OpTypes};

/// Which way the op turns: a pointer into an integer, or back.
#[derive(Clone, Copy)]
pub(super) enum PtrInt {
    /// `ptr_expose`: a pointer into an integer.
    Expose,
    /// `ptr_from_int`: an integer back into a pointer.
    FromInt,
}

impl PtrInt {
    /// The memory and the integer's width, when the op has its shape.
    fn shape(self, op: &OpTypes<'_>) -> Option<(u32, u32)> {
        let ([a], [r]) = (op.operands, op.results) else {
            return None;
        };
        match (self, core_type(a)?, core_type(r)?) {
            (Self::Expose, CoreType::Ptr(n), CoreType::Int(w))
            | (Self::FromInt, CoreType::Int(w), CoreType::Ptr(n)) => Some((n, w)),
            _ => None,
        }
    }
}

impl OpSpec for PtrInt {
    fn name(&self) -> &str {
        match self {
            Self::Expose => "ptr_expose",
            Self::FromInt => "ptr_from_int",
        }
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        if !op.attrs.is_empty() {
            return Err(format!("{} takes no attributes", self.name()));
        }
        if self.shape(op).is_some() {
            return Ok(OpShape::default());
        }
        let shape = match self {
            Self::Expose => "a pointer and defines an integer",
            Self::FromInt => "an integer and defines a pointer",
        };
        Err(format!(
            "{} takes {shape}, not {} -> {}",
            self.name(),
            type_list(op.operands),
            type_list(op.results)
        ))
    }

    /// Reads and allocates in its memory; `ptr_expose` may be UB
    /// (`Core.Op.effects`).
    fn effects(&self, op: &OpTypes<'_>) -> Effects {
        let memory = Memories::These(
            self.shape(op)
                .map(|(n, _)| n.to_string())
                .into_iter()
                .collect(),
        );
        Effects {
            reads: memory.clone(),
            allocates: memory,
            may_ub: matches!(self, Self::Expose),
            ..Effects::PURE
        }
    }

    fn addr_widths(&self, op: &OpTypes<'_>) -> Vec<(u32, u32)> {
        self.shape(op).into_iter().collect()
    }

    fn asks_addr_widths(&self) -> bool {
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialects::core::{MAX_MEMORY, float_type, int_type, ptr_type};
    use crate::{Attr, Type};

    fn types<'a>(attrs: &'a [Attr], operands: &'a [Type], results: &'a [Type]) -> OpTypes<'a> {
        OpTypes {
            attrs,
            operands,
            results,
        }
    }

    #[test]
    fn a_pointer_and_an_integer_of_any_width_decode_in_every_memory() {
        for (n, w) in [(0, 64), (0, 1), (1, 32), (MAX_MEMORY, 128)] {
            let (p, i) = ([ptr_type(n)], [int_type(w)]);
            let t = types(&[], &p, &i);
            assert_eq!(PtrInt::Expose.decode(&t), Ok(OpShape::default()));
            assert_eq!(PtrInt::Expose.addr_widths(&t), vec![(n, w)]);
            let t = types(&[], &i, &p);
            assert_eq!(PtrInt::FromInt.decode(&t), Ok(OpShape::default()));
            assert_eq!(PtrInt::FromInt.addr_widths(&t), vec![(n, w)]);
        }
    }

    #[test]
    fn every_other_shape_does_not_decode() {
        let (p, i64, f32) = (ptr_type(0), int_type(64), float_type(8, 23));
        for (attrs, operands, results) in [
            (
                vec![Attr::word("nonatomic")],
                vec![p.clone()],
                vec![i64.clone()],
            ),
            (vec![], vec![p.clone()], vec![p.clone()]),
            (vec![], vec![i64.clone()], vec![i64.clone()]),
            (vec![], vec![p.clone(), i64.clone()], vec![i64.clone()]),
            (vec![], vec![p.clone()], vec![]),
            (vec![], vec![f32.clone()], vec![i64.clone()]),
        ] {
            let t = types(&attrs, &operands, &results);
            assert!(
                PtrInt::Expose.decode(&t).is_err(),
                "{operands:?} {results:?}"
            );
            let t = types(&attrs, &results, &operands);
            assert!(
                PtrInt::FromInt.decode(&t).is_err(),
                "{results:?} {operands:?}"
            );
        }
    }

    #[test]
    fn each_reads_and_allocates_in_its_memory() {
        for n in [0, 1, 3] {
            let (p, i) = ([ptr_type(n)], [int_type(32)]);
            let memory = Memories::These(vec![n.to_string()]);
            assert_eq!(
                PtrInt::Expose.effects(&types(&[], &p, &i)),
                Effects {
                    reads: memory.clone(),
                    allocates: memory.clone(),
                    may_ub: true,
                    ..Effects::PURE
                }
            );
            assert_eq!(
                PtrInt::FromInt.effects(&types(&[], &i, &p)),
                Effects {
                    reads: memory.clone(),
                    allocates: memory,
                    ..Effects::PURE
                }
            );
        }
    }
}
