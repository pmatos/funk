//! The alignment that `alloca` and `load` write: `align(A)`, last among
//! their attributes and written only when the op gives an alignment
//! (`decodeAlign` in `lean/Fir/Core/AllocaText.lean`), and its rule in
//! validation, the data layout's rule for its own alignments
//! (`MemLayout.ValidAlign` in the Lean).

use crate::ir::MemLayout;
use crate::{Attr, Int};

/// Reads the attributes after an op's others: none, or `align(A)` with `A`
/// not negative. `Some(None)` when there are none, `None` when they do not
/// decode.
pub(super) fn decode_align(rest: &[Attr]) -> Option<Option<&Int>> {
    match rest {
        [] => Some(None),
        [Attr::App(h, args)] if h == "align" => match args.as_slice() {
            [Attr::Int(a)] if !a.is_negative() => Some(Some(a)),
            _ => None,
        },
        _ => None,
    }
}

/// Checks the alignment `a` that the op `op` writes, in decimal with no
/// sign, against the data layout's rule for its own alignments
/// (`MemLayout::valid_align`).
pub(super) fn check_align(op: &str, a: &str) -> Result<(), String> {
    match a.parse::<u32>() {
        Ok(n) if MemLayout::valid_align(n) => Ok(()),
        Ok(n) if !n.is_power_of_two() => {
            Err(format!("{op} aligns to a power of two of units, not {a}"))
        }
        _ => Err(format!(
            "{op} aligns to at most {} units, as the data layout does, not {a}",
            MemLayout::LIMIT
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn align(a: i128) -> Attr {
        Attr::App("align".into(), vec![Attr::int(a)])
    }

    #[test]
    fn decodes_no_attribute_or_one_align() {
        assert_eq!(decode_align(&[]), Some(None));
        assert_eq!(
            decode_align(&[align(4)]).map(|a| a.map(Int::as_str)),
            Some(Some("4"))
        );
        for bad in [
            vec![align(-4)],
            vec![Attr::int(4)],
            vec![align(4), align(4)],
            vec![Attr::App("align".into(), vec![])],
            vec![Attr::App("aligned".into(), vec![Attr::int(4)])],
        ] {
            assert_eq!(decode_align(&bad), None, "{bad:?}");
        }
    }

    #[test]
    fn checks_a_power_of_two_up_to_the_limit() {
        for a in ["1", "4", "8388608"] {
            assert_eq!(check_align("load", a), Ok(()), "{a}");
        }
        for a in ["0", "3", "16777216", "36893488147419103232"] {
            assert!(check_align("load", a).is_err(), "{a}");
        }
    }
}
