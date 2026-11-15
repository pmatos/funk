//! Stores: `store` (`decodeStore` in `lean/Fir/Core/StoreText.lean`,
//! `storeRule` in `lean/Fir/Core/Store.lean`, its rule in `Op.Valid` in
//! `lean/Fir/Core/Validation.lean`; #231).
//!
//! `store ORDERING [align(A)] %v, %p` stores the `iW` `%v` through the
//! pointer `%p` of `ptr<N>`, to memory `N`, and gives no result; a value of
//! `ptr<M>` is stored as its fragments (`storePtr`; stage 4d-2b of #231). Its
//! attributes are those of a load (`access.rs`): the ordering, then
//! `align(A)` when the op gives an alignment (ADR-2026-11-14-2316). It has
//! two operands, the integer or pointer value and then the pointer, and no
//! result. Any other shape does not decode.
//!
//! Validation accepts what it accepts of a load: the ordering `nonatomic`
//! and an alignment that is a power of two no larger than the data layout's
//! limit. With no `align(A)` the access is aligned to the natural alignment
//! of `iW` in memory `N`. The op writes memory `N` and may be UB (on a poison
//! pointer, or an access out of bounds, to a freed allocation, without
//! provenance or misaligned). It reads no memory: whether it faults depends
//! on the allocations, not on what their units hold. It gives no result, so
//! it makes no poison; a poison value is stored as poison units.

use super::access::Access;
use super::types::{CoreType, core_type};
use crate::effects::{Effects, MemSet};
use crate::registry::OpTypes;

/// The memory of the pointer `store` stores through, when it has an integer
/// or pointer operand, then a pointer operand, and no result.
fn memory(op: &OpTypes<'_>) -> Option<u32> {
    match (op.operands, op.results) {
        ([v, p], []) => match (core_type(v)?, core_type(p)?) {
            (CoreType::Int(_) | CoreType::Ptr(_), CoreType::Ptr(n)) => Some(n),
            _ => None,
        },
        _ => None,
    }
}

/// Writes its memory and may be UB (`Core.Op.effects`).
fn effects(writes: MemSet) -> Effects {
    Effects {
        writes,
        may_ub: true,
        ..Effects::PURE
    }
}

/// `store nonatomic align(4) %v, %p`.
pub(super) const STORE: Access = Access {
    name: "store",
    shape: "an integer or a pointer and then a pointer, and defines nothing",
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
                vec![Attr::word("seq_cst"), align(4)],
            ] {
                let operands = [int_type(w), ptr_type(n)];
                let op = types(&attrs, &operands, &[]);
                assert_eq!(STORE.decode(&op), Ok(OpShape::default()), "{attrs:?}");
            }
        }
    }

    #[test]
    fn a_pointer_of_any_memory_stores_through_a_pointer_of_any_memory() {
        for (m, n) in [(0, 0), (1, 0), (0, 1), (MAX_MEMORY, 2)] {
            let attrs = [Attr::word("nonatomic")];
            let operands = [ptr_type(m), ptr_type(n)];
            let op = types(&attrs, &operands, &[]);
            assert_eq!(STORE.decode(&op), Ok(OpShape::default()), "{m} {n}");
            assert_eq!(
                STORE.effects(&op).writes,
                MemSet::These(vec![n.to_string()]),
                "{m} {n}"
            );
        }
    }

    #[test]
    fn other_shapes_do_not_decode() {
        let (p, i32, f32) = (ptr_type(0), int_type(32), float_type(8, 23));
        let ok = [Attr::word("nonatomic")];
        for (attrs, operands, results) in [
            (vec![], vec![i32.clone(), p.clone()], vec![]),
            (ok.to_vec(), vec![p.clone(), i32.clone()], vec![]),
            (ok.to_vec(), vec![f32.clone(), p.clone()], vec![]),
            (ok.to_vec(), vec![i32.clone(), i32.clone()], vec![]),
            (ok.to_vec(), vec![p.clone()], vec![]),
            (ok.to_vec(), vec![i32.clone(), p.clone(), p.clone()], vec![]),
            (ok.to_vec(), vec![i32.clone(), p.clone()], vec![i32.clone()]),
        ] {
            let op = types(&attrs, &operands, &results);
            assert!(
                STORE.decode(&op).is_err(),
                "{attrs:?} {operands:?} {results:?}"
            );
        }
    }

    #[test]
    fn validation_names_the_store() {
        let operands = [int_type(32), ptr_type(0)];
        assert_eq!(
            check(&STORE, &[Attr::word("nonatomic"), align(4)], &operands, &[]),
            Ok(())
        );
        let e = check(&STORE, &[Attr::word("release")], &operands, &[]).unwrap_err();
        assert!(e.starts_with("store is nonatomic in M1"), "{e}");
        assert!(check(&STORE, &[Attr::word("nonatomic"), align(3)], &operands, &[]).is_err());
    }

    #[test]
    fn store_writes_its_memory_and_may_be_ub() {
        for n in [0, 1, 7] {
            let (attrs, operands) = ([Attr::word("nonatomic")], [int_type(8), ptr_type(n)]);
            assert_eq!(
                STORE.effects(&types(&attrs, &operands, &[])),
                Effects {
                    writes: MemSet::These(vec![n.to_string()]),
                    may_ub: true,
                    ..Effects::PURE
                }
            );
        }
    }
}
