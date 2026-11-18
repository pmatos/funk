//! The accesses of a memory, `load` and `store`, and the attributes they
//! share: the ordering, one of the words of [`ORDERINGS`] (`Ordering.word`
//! and `decodeOrdering` in `lean/Fir/Core/LoadText.lean`), then `align(A)`
//! when the op gives an alignment (ADR-2026-11-14-2316). A store writes them
//! as a load does (`decodeStore` in `lean/Fir/Core/StoreText.lean`).
//!
//! Validation accepts only the ordering `nonatomic`, the other orderings
//! being hooks for a concurrency model (ADR-2026-11-09-1542), and an
//! alignment that `check_align` accepts, as `alloca`'s is. Each access says
//! which shape it takes, how that shape names its memory, what it does to
//! that memory and whether it takes `align(A)`; [`Access`] does the rest.
//! `memcpy` and `memmove` take an ordering alone (ADR-2026-11-18-2131).

use super::align::{check_align, decode_align};
use super::type_list;
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

/// Reads the attributes of an access: its ordering and, when it `aligns`,
/// its alignment, or `None` when they do not decode.
fn access_attrs(attrs: &[Attr], aligns: bool) -> Option<(&str, Option<&Int>)> {
    let [Attr::Word(ordering), rest @ ..] = attrs else {
        return None;
    };
    if !ORDERINGS.contains(&ordering.as_str()) {
        return None;
    }
    match rest {
        [] => Some((ordering, None)),
        _ if aligns => Some((ordering, decode_align(rest)?)),
        _ => None,
    }
}

/// Checks the ordering and the alignment that the access `op` writes,
/// against M1's validation (`Op.Valid` in `lean/Fir/Core/Validation.lean`).
fn check_access(op: &str, ordering: &str, align: Option<&Int>) -> Result<(), String> {
    if ordering != "nonatomic" {
        return Err(format!(
            "{op} is nonatomic in M1, not {ordering}: the atomic orderings are hooks"
        ));
    }
    match align {
        Some(a) => check_align(op, a.as_str()),
        None => Ok(()),
    }
}

/// An access of a memory: its name, the shape it takes in words, the memory
/// of a shape it takes (`None` for any other), its effects given the
/// memory it uses, and whether it takes `align(A)`.
pub(super) struct Access {
    pub(super) name: &'static str,
    pub(super) shape: &'static str,
    pub(super) memory: fn(&OpTypes<'_>) -> Option<u32>,
    pub(super) effects: fn(MemSet) -> Effects,
    pub(super) aligns: bool,
}

impl OpSpec for Access {
    fn name(&self) -> &str {
        self.name
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        if (self.memory)(op).is_none() {
            return Err(format!(
                "{} takes {}, not {} -> {}",
                self.name,
                self.shape,
                type_list(op.operands),
                type_list(op.results)
            ));
        }
        if access_attrs(op.attrs, self.aligns).is_none() {
            let attrs = if self.aligns {
                "an ordering, then align(A) when given"
            } else {
                "an ordering alone"
            };
            return Err(format!("{} takes {attrs}", self.name));
        }
        Ok(OpShape::default())
    }

    fn check(&self, _cx: &OpContext<'_>, op: &OpTypes<'_>) -> Result<(), String> {
        match access_attrs(op.attrs, self.aligns) {
            Some((ordering, align)) => check_access(self.name, ordering, align),
            None => Ok(()),
        }
    }

    fn effects(&self, op: &OpTypes<'_>) -> Effects {
        let memory = (self.memory)(op).map_or(MemSet::NONE, |n| MemSet::These(vec![n.to_string()]));
        (self.effects)(memory)
    }
}

#[cfg(test)]
pub(super) mod tests {
    use super::*;
    use crate::{SymbolTable, Type};

    pub(in super::super) fn types<'a>(
        attrs: &'a [Attr],
        operands: &'a [Type],
        results: &'a [Type],
    ) -> OpTypes<'a> {
        OpTypes {
            attrs,
            operands,
            results,
        }
    }

    pub(in super::super) fn align(a: i128) -> Attr {
        Attr::App("align".into(), vec![Attr::int(a)])
    }

    /// Decodes and then checks `access` with the attributes `attrs`, the
    /// operands `operands` and the results `results`.
    pub(in super::super) fn check(
        access: &Access,
        attrs: &[Attr],
        operands: &[Type],
        results: &[Type],
    ) -> Result<(), String> {
        let symbols = SymbolTable::of(&[]);
        let cx = OpContext {
            symbols: &symbols,
            func: "f",
            results: &[],
        };
        let op = types(attrs, operands, results);
        access.decode(&op)?;
        access.check(&cx, &op)
    }

    #[test]
    fn every_ordering_decodes_with_or_without_an_alignment() {
        for o in ORDERINGS {
            assert_eq!(access_attrs(&[Attr::word(o)], true), Some((o, None)), "{o}");
            assert_eq!(
                access_attrs(&[Attr::word(o)], false),
                Some((o, None)),
                "{o}"
            );
            let attrs = [Attr::word(o), align(4)];
            assert_eq!(access_attrs(&attrs, false), None, "{o}");
            assert_eq!(
                access_attrs(&attrs, true).map(|(o, a)| (o, a.map(Int::as_str))),
                Some((o, Some("4"))),
                "{o}"
            );
        }
        assert_eq!(ORDERINGS.len(), 7);
    }

    #[test]
    fn other_attributes_do_not_decode() {
        for bad in [
            vec![],
            vec![Attr::word("relaxed")],
            vec![align(4), Attr::word("nonatomic")],
            vec![Attr::word("nonatomic"), align(-4)],
            vec![Attr::word("nonatomic"), Attr::int(4)],
        ] {
            assert_eq!(access_attrs(&bad, true), None, "{bad:?}");
        }
    }

    #[test]
    fn validation_accepts_only_nonatomic_and_valid_alignments() {
        let ok = |a| {
            check_access(
                "store",
                "nonatomic",
                Some(&Int::parse(a).expect("canonical")),
            )
        };
        assert_eq!(check_access("store", "nonatomic", None), Ok(()));
        for a in ["1", "8388608"] {
            assert_eq!(ok(a), Ok(()), "{a}");
        }
        for a in ["0", "3", "12", "16777216", "18446744073709551618"] {
            assert!(ok(a).is_err(), "{a}");
        }
        for o in &ORDERINGS[1..] {
            let e = check_access("store", o, None).unwrap_err();
            assert!(e.starts_with("store is nonatomic in M1"), "{e}");
        }
    }
}
