//! Fills: `memset` (`decodeMemSet` in `lean/Fir/Core/MemSetText.lean`,
//! `memSetRule` in `lean/Fir/Core/MemSet.lean`, its rule in `Op.Valid` and
//! `Op.unitWidths` in `lean/Fir/Core/Validation.lean`; #234,
//! ADR-2026-11-18-2131).
//!
//! `memset ORDERING %d, %v, %n` writes `%n` copies of the unit `%v` through
//! the pointer `%d` of `ptr<N>`, where `%v` is an integer and `%n` an
//! integer of any width read as unsigned, and gives no result. The one
//! attribute is the ordering; there is no `align(A)`, since each access is
//! aligned to one unit. An alignment and any other shape do not decode. It
//! is an [`Access`] that takes no alignment, and it asks that the data
//! layout give memory `N` units as wide as `%v`
//! ([`OpSpec::unit_widths`]), which the verifier checks with the rules of
//! the layout.
//!
//! Validation accepts only the ordering `nonatomic`. The op writes memory
//! `N` and may be UB: on a poison pointer and an access out of bounds, to a
//! freed allocation or without provenance, unless the length is 0, which
//! does nothing (the human's ruling of 2026-11-18 on #234). It gives no
//! result, so it makes no poison.

use super::access::Access;
use super::types::{CoreType, core_type};
use crate::effects::{Effects, MemSet as Memories};
use crate::registry::{OpContext, OpShape, OpSpec, OpTypes};

/// The memory of the op's pointer and the width of its value, when it takes
/// a pointer and then two integers, and has no result.
fn shape(op: &OpTypes<'_>) -> Option<(u32, u32)> {
    match (op.operands, op.results) {
        ([d, v, l], []) => match (core_type(d)?, core_type(v)?, core_type(l)?) {
            (CoreType::Ptr(n), CoreType::Int(w), CoreType::Int(_)) => Some((n, w)),
            _ => None,
        },
        _ => None,
    }
}

/// Writes its memory, and may be UB (`Core.Op.effects`).
fn effects(memory: Memories) -> Effects {
    Effects {
        writes: memory,
        may_ub: true,
        ..Effects::PURE
    }
}

const ACCESS: Access = Access {
    name: "memset",
    shape: "a pointer and then two integers, and defines nothing",
    memory: |op| shape(op).map(|(n, _)| n),
    effects,
    aligns: false,
};

/// `memset nonatomic %d, %v, %n`: the [`Access`] of a fill, which asks the
/// width of its memory's units.
pub(super) struct MemSet;

impl OpSpec for MemSet {
    fn name(&self) -> &str {
        ACCESS.name()
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        ACCESS.decode(op)
    }

    fn check(&self, cx: &OpContext<'_>, op: &OpTypes<'_>) -> Result<(), String> {
        ACCESS.check(cx, op)
    }

    fn effects(&self, op: &OpTypes<'_>) -> Effects {
        ACCESS.effects(op)
    }

    fn unit_widths(&self, op: &OpTypes<'_>) -> Vec<(u32, u32)> {
        shape(op).into_iter().collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Attr;
    use crate::dialects::core::access::ORDERINGS;
    use crate::dialects::core::access::tests::{align, check, types};
    use crate::dialects::core::{MAX_MEMORY, float_type, int_type, ptr_type};

    #[test]
    fn every_ordering_width_and_memory_decodes() {
        for (n, v, w) in [(0, 8, 64), (1, 16, 1), (MAX_MEMORY, 1, 128), (3, 32, 8)] {
            for o in ORDERINGS {
                let attrs = [Attr::word(o)];
                let operands = [ptr_type(n), int_type(v), int_type(w)];
                let t = types(&attrs, &operands, &[]);
                assert_eq!(MemSet.decode(&t), Ok(OpShape::default()), "{o} {n} {v} {w}");
                assert_eq!(MemSet.unit_widths(&t), vec![(n, v)]);
            }
        }
    }

    #[test]
    fn other_shapes_do_not_decode() {
        let (p, i8, i64) = (ptr_type(0), int_type(8), int_type(64));
        let ok = vec![Attr::word("nonatomic")];
        for (attrs, operands, results) in [
            (vec![], vec![p.clone(), i8.clone(), i64.clone()], vec![]),
            (
                vec![Attr::word("relaxed")],
                vec![p.clone(), i8.clone(), i64.clone()],
                vec![],
            ),
            (
                vec![Attr::word("nonatomic"), align(4)],
                vec![p.clone(), i8.clone(), i64.clone()],
                vec![],
            ),
            (ok.clone(), vec![p.clone(), p.clone(), i64.clone()], vec![]),
            (
                ok.clone(),
                vec![i64.clone(), i8.clone(), i64.clone()],
                vec![],
            ),
            (
                ok.clone(),
                vec![p.clone(), float_type(8, 23), i64.clone()],
                vec![],
            ),
            (ok.clone(), vec![p.clone(), i8.clone()], vec![]),
            (
                ok.clone(),
                vec![p.clone(), i8.clone(), i64.clone()],
                vec![i64.clone()],
            ),
        ] {
            let t = types(&attrs, &operands, &results);
            assert!(
                MemSet.decode(&t).is_err(),
                "{attrs:?} {operands:?} {results:?}"
            );
        }
    }

    #[test]
    fn validation_accepts_only_nonatomic() {
        let operands = [ptr_type(0), int_type(8), int_type(64)];
        assert_eq!(
            check(&ACCESS, &[Attr::word("nonatomic")], &operands, &[]),
            Ok(())
        );
        let e = check(&ACCESS, &[Attr::word("seq_cst")], &operands, &[]).unwrap_err();
        assert!(e.starts_with("memset is nonatomic in M1"), "{e}");
    }

    #[test]
    fn it_writes_its_memory_and_may_be_ub() {
        for n in [0, 1, 3] {
            let (attrs, operands) = (
                [Attr::word("nonatomic")],
                [ptr_type(n), int_type(16), int_type(8)],
            );
            assert_eq!(
                MemSet.effects(&types(&attrs, &operands, &[])),
                Effects {
                    writes: Memories::These(vec![n.to_string()]),
                    may_ub: true,
                    ..Effects::PURE
                }
            );
        }
    }
}
