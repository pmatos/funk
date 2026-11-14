//! Loads: `load` (`decodeLoad` in `lean/Fir/Core/LoadText.lean`, `loadRule`
//! in `lean/Fir/Core/Load.lean`, its rule in `Op.Valid` in
//! `lean/Fir/Core/Validation.lean`; #231).
//!
//! `%v: iW = load ORDERING [align(A)] %p` loads an `iW` through the pointer
//! `%p` of `ptr<N>`, from memory `N`. Its attributes are, in order: the
//! ordering, one of the words of [`ORDERINGS`]; and `align(A)`, with `A` not
//! negative, written only when the op gives an alignment. It has one pointer
//! operand and one integer result. Any other shape does not decode.
//!
//! Validation accepts only the ordering `nonatomic`, the other orderings
//! being hooks for a concurrency model (ADR-2026-11-09-1542), and an
//! alignment that is a power of two no larger than [`MemLayout::LIMIT`], as
//! `alloca`'s is. With no `align(A)` the access is aligned to the natural
//! alignment of `iW` in memory `N`. The op reads memory `N`, may be UB (on a
//! poison pointer, or an access out of bounds, to a freed allocation,
//! without provenance or misaligned) and may give poison (units that are not
//! an integer's encoding, as fresh memory's).
//!
//! [`MemLayout::LIMIT`]: crate::ir::MemLayout::LIMIT

use super::alloca::check_align;
use super::type_list;
use super::types::{CoreType, core_type};
use crate::effects::{Effects, MemSet};
use crate::registry::{OpContext, OpShape, OpSpec, OpTypes};
use crate::{Attr, Int};

/// The orderings of an access, as words (`Ordering.word`).
pub const ORDERINGS: [&str; 7] = [
    "nonatomic",
    "unordered",
    "monotonic",
    "acquire",
    "release",
    "acq_rel",
    "seq_cst",
];

/// Reads the attributes of `load`: its ordering and its alignment, or
/// `None` when they do not decode.
fn parts(attrs: &[Attr]) -> Option<(&str, Option<&Int>)> {
    let [Attr::Word(ordering), rest @ ..] = attrs else {
        return None;
    };
    if !ORDERINGS.contains(&ordering.as_str()) {
        return None;
    }
    let align = match rest {
        [] => None,
        [Attr::App(h, args)] if h == "align" => match args.as_slice() {
            [Attr::Int(a)] if !a.is_negative() => Some(a),
            _ => return None,
        },
        _ => return None,
    };
    Some((ordering, align))
}

/// The memory of the pointer `load` loads through, when it has one pointer
/// operand and one integer result.
fn memory(op: &OpTypes<'_>) -> Option<u32> {
    match (op.operands, op.results) {
        ([p], [r]) => match (core_type(p)?, core_type(r)?) {
            (CoreType::Ptr(n), CoreType::Int(_)) => Some(n),
            _ => None,
        },
        _ => None,
    }
}

/// `%v: i32 = load nonatomic align(4) %p`.
pub(super) struct Load;

impl OpSpec for Load {
    fn name(&self) -> &str {
        "load"
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        if memory(op).is_none() {
            return Err(format!(
                "load takes a pointer and defines an integer, not {} -> {}",
                type_list(op.operands),
                type_list(op.results)
            ));
        }
        if parts(op.attrs).is_none() {
            return Err("load takes an ordering, then align(A) when given".into());
        }
        Ok(OpShape::default())
    }

    fn check(&self, _cx: &OpContext<'_>, op: &OpTypes<'_>) -> Result<(), String> {
        let Some((ordering, align)) = parts(op.attrs) else {
            return Ok(());
        };
        if ordering != "nonatomic" {
            return Err(format!(
                "load is nonatomic in M1, not {ordering}: the atomic orderings are hooks"
            ));
        }
        match align {
            Some(a) => check_align("load", a.as_str()),
            None => Ok(()),
        }
    }

    /// Reads its memory, may be UB and may give poison (`Core.Op.effects`).
    fn effects(&self, op: &OpTypes<'_>) -> Effects {
        Effects {
            reads: memory(op).map_or(MemSet::NONE, |n| MemSet::These(vec![n.to_string()])),
            may_ub: true,
            may_poison: true,
            ..Effects::PURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialects::core::{MAX_MEMORY, float_type, int_type, ptr_type};
    use crate::{SymbolTable, Type};

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
        let (operands, results) = ([ptr_type(0)], [int_type(32)]);
        let op = types(attrs, &operands, &results);
        Load.decode(&op)?;
        Load.check(&cx, &op)
    }

    #[test]
    fn every_ordering_and_memory_decodes() {
        for (o, n, w) in [
            ("nonatomic", 0, 32),
            ("seq_cst", 1, 1),
            ("acq_rel", MAX_MEMORY, 128),
        ] {
            for attrs in [vec![word(o)], vec![word(o), align(4)]] {
                let (operands, results) = ([ptr_type(n)], [int_type(w)]);
                let op = types(&attrs, &operands, &results);
                assert_eq!(Load.decode(&op), Ok(OpShape::default()), "{attrs:?}");
            }
        }
        assert_eq!(ORDERINGS.len(), 7);
    }

    #[test]
    fn other_shapes_do_not_decode() {
        let (p, i32, f32) = (ptr_type(0), int_type(32), float_type(8, 23));
        let ok = [word("nonatomic")];
        for (attrs, operands, results) in [
            (vec![], vec![p.clone()], vec![i32.clone()]),
            (vec![word("relaxed")], vec![p.clone()], vec![i32.clone()]),
            (
                vec![word("nonatomic"), align(-4)],
                vec![p.clone()],
                vec![i32.clone()],
            ),
            (
                vec![word("nonatomic"), Attr::int(4)],
                vec![p.clone()],
                vec![i32.clone()],
            ),
            (
                vec![align(4), word("nonatomic")],
                vec![p.clone()],
                vec![i32.clone()],
            ),
            (ok.to_vec(), vec![p.clone()], vec![p.clone()]),
            (ok.to_vec(), vec![p.clone()], vec![f32.clone()]),
            (ok.to_vec(), vec![i32.clone()], vec![i32.clone()]),
            (ok.to_vec(), vec![p.clone(), p.clone()], vec![i32.clone()]),
            (ok.to_vec(), vec![], vec![i32.clone()]),
            (ok.to_vec(), vec![p.clone()], vec![]),
        ] {
            let op = types(&attrs, &operands, &results);
            assert!(
                Load.decode(&op).is_err(),
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
            assert!(e.starts_with("load is nonatomic in M1"), "{e}");
        }
        for a in [0, 3, 12, 1 << 24, (1 << 64) + 2] {
            assert!(check(&[word("nonatomic"), align(a)]).is_err(), "{a}");
        }
    }

    #[test]
    fn load_reads_its_memory_and_may_be_ub_or_poison() {
        for n in [0, 1, 7] {
            let (attrs, operands, results) = ([word("nonatomic")], [ptr_type(n)], [int_type(8)]);
            let effects = Load.effects(&types(&attrs, &operands, &results));
            assert_eq!(
                effects,
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
