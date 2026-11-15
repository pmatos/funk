//! Stores: `store` (`decodeStore` in `lean/Fir/Core/StoreText.lean`,
//! `storeRule` in `lean/Fir/Core/Store.lean`, its rule in `Op.Valid` in
//! `lean/Fir/Core/Validation.lean`; #231).
//!
//! `store ORDERING [align(A)] %v, %p` stores the `iW` `%v` through the
//! pointer `%p` of `ptr<N>`, to memory `N`, and gives no result. Its
//! attributes are those of a load (`access.rs`): the ordering, then
//! `align(A)` when the op gives an alignment (ADR-2026-11-14-2316). It has
//! two operands, the integer value and then the pointer, and no result. Any
//! other shape does not decode.
//!
//! Validation accepts what it accepts of a load: the ordering `nonatomic`
//! and an alignment that is a power of two no larger than the data layout's
//! limit. With no `align(A)` the access is aligned to the natural alignment
//! of `iW` in memory `N`. The op writes memory `N` and may be UB (on a poison
//! pointer, or an access out of bounds, to a freed allocation, without
//! provenance or misaligned). It reads no memory: whether it faults depends
//! on the allocations, not on what their units hold. It gives no result, so
//! it makes no poison; a poison value is stored as poison units.

use super::access::{access_attrs, check_access};
use super::type_list;
use super::types::{CoreType, core_type};
use crate::effects::{Effects, MemSet};
use crate::registry::{OpContext, OpShape, OpSpec, OpTypes};

/// The memory of the pointer `store` stores through, when it has an integer
/// operand, then a pointer operand, and no result.
fn memory(op: &OpTypes<'_>) -> Option<u32> {
    match (op.operands, op.results) {
        ([v, p], []) => match (core_type(v)?, core_type(p)?) {
            (CoreType::Int(_), CoreType::Ptr(n)) => Some(n),
            _ => None,
        },
        _ => None,
    }
}

/// `store nonatomic align(4) %v, %p`.
pub(super) struct Store;

impl OpSpec for Store {
    fn name(&self) -> &str {
        "store"
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        if memory(op).is_none() {
            return Err(format!(
                "store takes an integer and then a pointer, and defines nothing, not {} -> {}",
                type_list(op.operands),
                type_list(op.results)
            ));
        }
        if access_attrs(op.attrs).is_none() {
            return Err("store takes an ordering, then align(A) when given".into());
        }
        Ok(OpShape::default())
    }

    fn check(&self, _cx: &OpContext<'_>, op: &OpTypes<'_>) -> Result<(), String> {
        match access_attrs(op.attrs) {
            Some((ordering, align)) => check_access("store", ordering, align),
            None => Ok(()),
        }
    }

    /// Writes its memory and may be UB (`Core.Op.effects`).
    fn effects(&self, op: &OpTypes<'_>) -> Effects {
        Effects {
            writes: memory(op).map_or(MemSet::NONE, |n| MemSet::These(vec![n.to_string()])),
            may_ub: true,
            ..Effects::PURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialects::core::{MAX_MEMORY, ORDERINGS, float_type, int_type, ptr_type};
    use crate::{Attr, SymbolTable, Type};

    fn types<'a>(attrs: &'a [Attr], operands: &'a [Type], results: &'a [Type]) -> OpTypes<'a> {
        OpTypes {
            attrs,
            operands,
            results,
        }
    }

    fn word(w: &str) -> Attr {
        Attr::word(w)
    }

    fn align(a: i128) -> Attr {
        Attr::App("align".into(), vec![Attr::int(a)])
    }

    fn check(attrs: &[Attr]) -> Result<(), String> {
        let symbols = SymbolTable::of(&[]);
        let cx = OpContext {
            symbols: &symbols,
            func: "f",
            results: &[],
        };
        let operands = [int_type(32), ptr_type(0)];
        let op = types(attrs, &operands, &[]);
        Store.decode(&op)?;
        Store.check(&cx, &op)
    }

    #[test]
    fn every_ordering_width_and_memory_decodes() {
        for (o, n, w) in [
            ("nonatomic", 0, 32),
            ("release", 1, 1),
            ("seq_cst", MAX_MEMORY, 128),
        ] {
            for attrs in [vec![word(o)], vec![word(o), align(4)]] {
                let operands = [int_type(w), ptr_type(n)];
                let op = types(&attrs, &operands, &[]);
                assert_eq!(Store.decode(&op), Ok(OpShape::default()), "{attrs:?}");
            }
        }
    }

    #[test]
    fn other_shapes_do_not_decode() {
        let (p, i32, f32) = (ptr_type(0), int_type(32), float_type(8, 23));
        let ok = [word("nonatomic")];
        for (attrs, operands, results) in [
            (vec![], vec![i32.clone(), p.clone()], vec![]),
            (vec![word("relaxed")], vec![i32.clone(), p.clone()], vec![]),
            (
                vec![word("nonatomic"), align(-4)],
                vec![i32.clone(), p.clone()],
                vec![],
            ),
            (
                vec![align(4), word("nonatomic")],
                vec![i32.clone(), p.clone()],
                vec![],
            ),
            (ok.to_vec(), vec![p.clone(), i32.clone()], vec![]),
            (ok.to_vec(), vec![f32.clone(), p.clone()], vec![]),
            (ok.to_vec(), vec![p.clone(), p.clone()], vec![]),
            (ok.to_vec(), vec![i32.clone(), i32.clone()], vec![]),
            (ok.to_vec(), vec![p.clone()], vec![]),
            (ok.to_vec(), vec![i32.clone(), p.clone(), p.clone()], vec![]),
            (ok.to_vec(), vec![i32.clone(), p.clone()], vec![i32.clone()]),
        ] {
            let op = types(&attrs, &operands, &results);
            assert!(
                Store.decode(&op).is_err(),
                "{attrs:?} {operands:?} {results:?}"
            );
        }
    }

    #[test]
    fn validation_accepts_only_nonatomic_and_valid_alignments() {
        for attrs in [
            vec![word("nonatomic")],
            vec![word("nonatomic"), align(1)],
            vec![word("nonatomic"), align(1 << 23)],
        ] {
            assert_eq!(check(&attrs), Ok(()), "{attrs:?}");
        }
        for o in &ORDERINGS[1..] {
            let e = check(&[word(o)]).unwrap_err();
            assert!(e.starts_with("store is nonatomic in M1"), "{e}");
        }
        for a in [0, 3, 12, 1 << 24, (1 << 64) + 2] {
            assert!(check(&[word("nonatomic"), align(a)]).is_err(), "{a}");
        }
    }

    #[test]
    fn store_writes_its_memory_and_may_be_ub() {
        for n in [0, 1, 7] {
            let (attrs, operands) = ([word("nonatomic")], [int_type(8), ptr_type(n)]);
            let effects = Store.effects(&types(&attrs, &operands, &[]));
            assert_eq!(
                effects,
                Effects {
                    writes: MemSet::These(vec![n.to_string()]),
                    may_ub: true,
                    ..Effects::PURE
                }
            );
        }
    }
}
