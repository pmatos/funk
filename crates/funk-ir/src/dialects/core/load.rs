//! Loads: `load` (`decodeLoad` in `lean/Fir/Core/LoadText.lean`, `loadRule`
//! in `lean/Fir/Core/Load.lean`, its rule in `Op.Valid` in
//! `lean/Fir/Core/Validation.lean`; #231).
//!
//! `%v: iW = load ORDERING [align(A)] %p` loads an `iW` through the pointer
//! `%p` of `ptr<N>`, from memory `N`, and `%r: ptr<M> = load ...` loads a
//! pointer of memory `M` (`loadPtr`; stage 4d-2b of #231). Its attributes
//! are those of an access (`access.rs`), in order: the ordering, one of the
//! words of [`ORDERINGS`]; and `align(A)`, with `A` not negative, written
//! only when the op gives an alignment. It has one pointer operand and one
//! integer or pointer result. Any other shape does not decode.
//!
//! Validation accepts only the ordering `nonatomic`, the other orderings
//! being hooks for a concurrency model (ADR-2026-11-09-1542), and an
//! alignment that is a power of two no larger than [`MemLayout::LIMIT`], as
//! `alloca`'s is. With no `align(A)` the access is aligned to the natural
//! alignment of `iW` in memory `N`, or to the default alignment of `ptr<M>`
//! there, as `alloca`'s. The op reads memory `N`, may be UB (on a poison
//! pointer, or an access out of bounds, to a freed allocation, without
//! provenance or misaligned) and may give poison (units that are not an
//! encoding of its type, as fresh memory's, or a punned load).
//!
//! [`MemLayout::LIMIT`]: crate::ir::MemLayout::LIMIT
//! [`ORDERINGS`]: super::ORDERINGS

use super::access::Access;
use super::types::{CoreType, core_type};
use crate::effects::{Effects, MemSet};
use crate::registry::OpTypes;

/// The memory of the pointer `load` loads through, when it has one pointer
/// operand and one integer or pointer result.
fn memory(op: &OpTypes<'_>) -> Option<u32> {
    match (op.operands, op.results) {
        ([p], [r]) => match (core_type(p)?, core_type(r)?) {
            (CoreType::Ptr(n), CoreType::Int(_) | CoreType::Ptr(_)) => Some(n),
            _ => None,
        },
        _ => None,
    }
}

/// Reads its memory, may be UB and may give poison (`Core.Op.effects`).
fn effects(reads: MemSet) -> Effects {
    Effects {
        reads,
        may_ub: true,
        may_poison: true,
        ..Effects::PURE
    }
}

/// `%v: i32 = load nonatomic align(4) %p`.
pub(super) const LOAD: Access = Access {
    name: "load",
    shape: "a pointer and defines an integer or a pointer",
    memory,
    effects,
};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Attr;
    use crate::dialects::core::access::tests::{align, check, types};
    use crate::dialects::core::{MAX_MEMORY, float_type, int_type, ptr_type};
    use crate::registry::{OpShape, OpSpec};

    #[test]
    fn every_width_and_memory_decodes() {
        for (n, w) in [(0, 32), (1, 1), (MAX_MEMORY, 128)] {
            for attrs in [
                vec![Attr::word("nonatomic")],
                vec![Attr::word("acq_rel"), align(4)],
            ] {
                let (operands, results) = ([ptr_type(n)], [int_type(w)]);
                let op = types(&attrs, &operands, &results);
                assert_eq!(LOAD.decode(&op), Ok(OpShape::default()), "{attrs:?}");
            }
        }
    }

    #[test]
    fn a_pointer_of_any_memory_loads_through_a_pointer_of_any_memory() {
        for (n, m) in [(0, 0), (1, 0), (0, 1), (MAX_MEMORY, 2)] {
            let attrs = [Attr::word("nonatomic")];
            let (operands, results) = ([ptr_type(n)], [ptr_type(m)]);
            let op = types(&attrs, &operands, &results);
            assert_eq!(LOAD.decode(&op), Ok(OpShape::default()), "{n} {m}");
            assert_eq!(
                LOAD.effects(&op).reads,
                MemSet::These(vec![n.to_string()]),
                "{n} {m}"
            );
        }
    }

    #[test]
    fn other_shapes_do_not_decode() {
        let (p, i32, f32) = (ptr_type(0), int_type(32), float_type(8, 23));
        let ok = [Attr::word("nonatomic")];
        for (attrs, operands, results) in [
            (vec![], vec![p.clone()], vec![i32.clone()]),
            (ok.to_vec(), vec![p.clone()], vec![f32.clone()]),
            (ok.to_vec(), vec![i32.clone()], vec![i32.clone()]),
            (ok.to_vec(), vec![p.clone(), p.clone()], vec![i32.clone()]),
            (ok.to_vec(), vec![], vec![i32.clone()]),
            (ok.to_vec(), vec![p.clone()], vec![]),
        ] {
            let op = types(&attrs, &operands, &results);
            assert!(
                LOAD.decode(&op).is_err(),
                "{attrs:?} {operands:?} {results:?}"
            );
        }
    }

    #[test]
    fn validation_names_the_load() {
        let (operands, results) = ([ptr_type(0)], [int_type(32)]);
        assert_eq!(
            check(
                &LOAD,
                &[Attr::word("nonatomic"), align(4)],
                &operands,
                &results
            ),
            Ok(())
        );
        let e = check(&LOAD, &[Attr::word("acquire")], &operands, &results).unwrap_err();
        assert!(e.starts_with("load is nonatomic in M1"), "{e}");
        assert!(
            check(
                &LOAD,
                &[Attr::word("nonatomic"), align(3)],
                &operands,
                &results
            )
            .is_err()
        );
    }

    #[test]
    fn load_reads_its_memory_and_may_be_ub_or_poison() {
        for n in [0, 1, 7] {
            let (attrs, operands, results) =
                ([Attr::word("nonatomic")], [ptr_type(n)], [int_type(8)]);
            assert_eq!(
                LOAD.effects(&types(&attrs, &operands, &results)),
                Effects {
                    reads: MemSet::These(vec![n.to_string()]),
                    may_ub: true,
                    may_poison: true,
                    ..Effects::PURE
                }
            );
        }
    }
}
