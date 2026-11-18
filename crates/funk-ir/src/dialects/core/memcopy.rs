//! Copies and moves: `memcpy` and `memmove` (`decodeMemCopy` in
//! `lean/Fir/Core/MemCopyText.lean`, `memCopyRule` in
//! `lean/Fir/Core/MemCopy.lean`, its rule in `Op.Valid` in
//! `lean/Fir/Core/Validation.lean`; #234, ADR-2026-11-18-2131).
//!
//! `memcpy ORDERING %d, %s, %n` carries `%n` units of memory `N` from the
//! pointer `%s` to the pointer `%d`, both of `ptr<N>`, where `%n` is an
//! integer of any width read as unsigned, and gives no result; `memmove`
//! does the same with ranges that may overlap. The one attribute is the
//! ordering, a word of [`ORDERINGS`]; there is no `align(A)`, since each
//! access is aligned to one unit. Pointers of two memories, an alignment
//! and any other shape do not decode.
//!
//! Validation accepts only the ordering `nonatomic`. The op reads and
//! writes memory `N` and may be UB: on a poison pointer, an access out of
//! bounds, to a freed allocation or without provenance, and, for `memcpy`,
//! ranges that partly overlap, unless the length is 0, which does nothing
//! (the human's rulings of 2026-11-18 on #234). It gives no result, so it
//! makes no poison.

use super::access::{ORDERINGS, check_access};
use super::type_list;
use super::types::{CoreType, core_type};
use crate::Attr;
use crate::effects::{Effects, MemSet};
use crate::registry::{OpContext, OpShape, OpSpec, OpTypes};

/// A copy, `memcpy`, or a move, `memmove`, by its name.
pub(super) struct MemCopy(pub(super) &'static str);

/// The ordering that the op writes, when it writes one word of
/// [`ORDERINGS`] and nothing else.
fn ordering(attrs: &[Attr]) -> Option<&str> {
    match attrs {
        [Attr::Word(o)] if ORDERINGS.contains(&o.as_str()) => Some(o),
        _ => None,
    }
}

/// The memory of the op's pointers, when it takes two pointers of one
/// memory and then an integer, and has no result.
fn memory(op: &OpTypes<'_>) -> Option<u32> {
    match (op.operands, op.results) {
        ([d, s, l], []) => match (core_type(d)?, core_type(s)?, core_type(l)?) {
            (CoreType::Ptr(n), CoreType::Ptr(m), CoreType::Int(_)) if n == m => Some(n),
            _ => None,
        },
        _ => None,
    }
}

impl OpSpec for MemCopy {
    fn name(&self) -> &str {
        self.0
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        if memory(op).is_none() {
            return Err(format!(
                "{} takes two pointers of one memory and then an integer, and defines \
                 nothing, not {} -> {}",
                self.0,
                type_list(op.operands),
                type_list(op.results)
            ));
        }
        if ordering(op.attrs).is_none() {
            return Err(format!("{} takes an ordering alone", self.0));
        }
        Ok(OpShape::default())
    }

    fn check(&self, _cx: &OpContext<'_>, op: &OpTypes<'_>) -> Result<(), String> {
        ordering(op.attrs).map_or(Ok(()), |o| check_access(self.0, o, None))
    }

    /// Reads and writes its memory, and may be UB (`Core.Op.effects`).
    fn effects(&self, op: &OpTypes<'_>) -> Effects {
        let memory = memory(op).map_or(MemSet::NONE, |n| MemSet::These(vec![n.to_string()]));
        Effects {
            reads: memory.clone(),
            writes: memory,
            may_ub: true,
            ..Effects::PURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialects::core::access::tests::{align, types};
    use crate::dialects::core::{MAX_MEMORY, int_type, ptr_type};
    use crate::{SymbolTable, Type};

    const OPS: [MemCopy; 2] = [MemCopy("memcpy"), MemCopy("memmove")];

    fn check(op: &MemCopy, attrs: &[Attr], operands: &[Type]) -> Result<(), String> {
        let symbols = SymbolTable::of(&[]);
        let cx = OpContext {
            symbols: &symbols,
            func: "f",
            results: &[],
        };
        let t = types(attrs, operands, &[]);
        op.decode(&t)?;
        op.check(&cx, &t)
    }

    #[test]
    fn every_ordering_width_and_memory_decodes() {
        for op in &OPS {
            for (n, w) in [(0, 64), (1, 1), (MAX_MEMORY, 128), (3, 8)] {
                for o in ORDERINGS {
                    let attrs = [Attr::word(o)];
                    let operands = [ptr_type(n), ptr_type(n), int_type(w)];
                    let t = types(&attrs, &operands, &[]);
                    assert_eq!(
                        op.decode(&t),
                        Ok(OpShape::default()),
                        "{} {o} {n} {w}",
                        op.0
                    );
                }
            }
        }
    }

    #[test]
    fn other_shapes_do_not_decode() {
        let (p, q, i64) = (ptr_type(0), ptr_type(1), int_type(64));
        let ok = vec![Attr::word("nonatomic")];
        for op in &OPS {
            for (attrs, operands, results) in [
                (vec![], vec![p.clone(), p.clone(), i64.clone()], vec![]),
                (
                    vec![Attr::word("relaxed")],
                    vec![p.clone(), p.clone(), i64.clone()],
                    vec![],
                ),
                (
                    vec![Attr::word("nonatomic"), align(4)],
                    vec![p.clone(), p.clone(), i64.clone()],
                    vec![],
                ),
                (ok.clone(), vec![p.clone(), q.clone(), i64.clone()], vec![]),
                (
                    ok.clone(),
                    vec![i64.clone(), p.clone(), i64.clone()],
                    vec![],
                ),
                (ok.clone(), vec![p.clone(), p.clone(), p.clone()], vec![]),
                (ok.clone(), vec![p.clone(), p.clone()], vec![]),
                (
                    ok.clone(),
                    vec![p.clone(), p.clone(), i64.clone()],
                    vec![i64.clone()],
                ),
            ] {
                let t = types(&attrs, &operands, &results);
                assert!(
                    op.decode(&t).is_err(),
                    "{} {attrs:?} {operands:?} {results:?}",
                    op.0
                );
            }
        }
    }

    #[test]
    fn validation_accepts_only_nonatomic() {
        let operands = [ptr_type(0), ptr_type(0), int_type(64)];
        for op in &OPS {
            assert_eq!(check(op, &[Attr::word("nonatomic")], &operands), Ok(()));
            let e = check(op, &[Attr::word("seq_cst")], &operands).unwrap_err();
            assert!(
                e.starts_with(&format!("{} is nonatomic in M1", op.0)),
                "{e}"
            );
        }
    }

    #[test]
    fn it_reads_and_writes_its_memory_and_may_be_ub() {
        for op in &OPS {
            for n in [0, 1, 3] {
                let (attrs, operands) = (
                    [Attr::word("nonatomic")],
                    [ptr_type(n), ptr_type(n), int_type(8)],
                );
                assert_eq!(
                    op.effects(&types(&attrs, &operands, &[])),
                    Effects {
                        reads: MemSet::These(vec![n.to_string()]),
                        writes: MemSet::These(vec![n.to_string()]),
                        may_ub: true,
                        ..Effects::PURE
                    }
                );
            }
        }
    }
}
