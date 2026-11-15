//! The attributes that `load` and `store` share, the accesses of a memory:
//! the ordering, one of the words of [`ORDERINGS`] (`Ordering.word` and
//! `decodeOrdering` in `lean/Fir/Core/LoadText.lean`), then `align(A)` when
//! the op gives an alignment (ADR-2026-11-14-2316). A store writes them as a
//! load does (`decodeStore` in `lean/Fir/Core/StoreText.lean`).
//!
//! Validation accepts only the ordering `nonatomic`, the other orderings
//! being hooks for a concurrency model (ADR-2026-11-09-1542), and an
//! alignment that `check_align` accepts, as `alloca`'s is.

use super::align::{check_align, decode_align};
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

/// Reads the attributes of an access: its ordering and its alignment, or
/// `None` when they do not decode.
pub(super) fn access_attrs(attrs: &[Attr]) -> Option<(&str, Option<&Int>)> {
    let [Attr::Word(ordering), rest @ ..] = attrs else {
        return None;
    };
    if !ORDERINGS.contains(&ordering.as_str()) {
        return None;
    }
    Some((ordering, decode_align(rest)?))
}

/// Checks the ordering and the alignment that the access `op` writes,
/// against M1's validation (`Op.Valid` in `lean/Fir/Core/Validation.lean`).
pub(super) fn check_access(op: &str, ordering: &str, align: Option<&Int>) -> Result<(), String> {
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

#[cfg(test)]
mod tests {
    use super::*;

    fn align(a: i128) -> Attr {
        Attr::App("align".into(), vec![Attr::int(a)])
    }

    #[test]
    fn every_ordering_decodes_with_or_without_an_alignment() {
        for o in ORDERINGS {
            assert_eq!(access_attrs(&[Attr::word(o)]), Some((o, None)), "{o}");
            let attrs = [Attr::word(o), align(4)];
            assert_eq!(
                access_attrs(&attrs).map(|(o, a)| (o, a.map(Int::as_str))),
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
            assert_eq!(access_attrs(&bad), None, "{bad:?}");
        }
    }

    #[test]
    fn validation_accepts_only_nonatomic_and_valid_alignments() {
        assert_eq!(check_access("store", "nonatomic", None), Ok(()));
        for o in &ORDERINGS[1..] {
            let e = check_access("store", o, None).unwrap_err();
            assert!(e.starts_with("store is nonatomic in M1"), "{e}");
        }
        let three = Int::parse("3").expect("a canonical integer");
        assert!(check_access("store", "nonatomic", Some(&three)).is_err());
    }
}
