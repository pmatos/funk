//! Division and remainder: `sdiv`, `udiv`, `srem` and `urem` (`Op.decode`
//! and `decodeExact` in `lean/Fir/Core/Text.lean`).
//!
//! Each op takes two `iN` and defines one `iN`. `sdiv` and `udiv` have one
//! flag, `exact`, written at most once; `srem` and `urem` have no attributes.
//! So `sdiv exact exact`, `udiv nsw` and `srem exact` do not decode. A broken
//! `exact` gives poison and a zero divisor is immediate UB, at run time, so
//! validation has no rule for these ops beyond their signature (`Op.Valid`
//! in `lean/Fir/Core/Validation.lean`).

use super::arith::bin_width;
use super::type_list;
use crate::Attr;
use crate::registry::{OpShape, OpSpec, OpTypes};

/// The division and remainder ops, each with whether it may have the flag
/// `exact`.
pub const DIVISION_OPS: [(&str, bool); 4] = [
    ("sdiv", true),
    ("udiv", true),
    ("srem", false),
    ("urem", false),
];

/// Checks that the attributes of the op `op` are none, or `exact` alone
/// when `exact` is one of its flags (`decodeExact`), or says why not.
fn decode_flags(op: &str, exact: bool, attrs: &[Attr]) -> Result<(), String> {
    if !exact && !attrs.is_empty() {
        return Err(format!("{op} takes no attributes"));
    }
    for a in attrs {
        match a {
            Attr::Word(w) if w == "exact" => {}
            Attr::Word(w) => return Err(format!("{op}'s flag is exact, not {w}")),
            _ => return Err(format!("{op}'s attributes are its flag exact, not {a}")),
        }
    }
    if attrs.len() > 1 {
        return Err(format!("{op} has the flag exact more than once"));
    }
    Ok(())
}

/// `%q: iN = sdiv %a, %b`, and `udiv`, `srem` and `urem` likewise: the
/// op's name, and whether it may have the flag `exact`.
pub(super) struct Division(pub &'static str, pub bool);

impl OpSpec for Division {
    fn name(&self) -> &str {
        self.0
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        decode_flags(self.0, self.1, op.attrs)?;
        match bin_width(op.operands, op.results) {
            Some(_) => Ok(OpShape::default()),
            None => Err(format!(
                "{} takes two operands of one integer type and defines one value of that \
                 type, not {} -> {}",
                self.0,
                type_list(op.operands),
                type_list(op.results)
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn flags(op: &str, attrs: &[Attr]) -> Result<(), String> {
        let exact = DIVISION_OPS.iter().any(|&(o, e)| o == op && e);
        decode_flags(op, exact, attrs)
    }

    fn words(ws: &[&str]) -> Vec<Attr> {
        ws.iter().map(|w| Attr::word(*w)).collect()
    }

    #[test]
    fn flags_decode_as_decode_exact_reads_them() {
        for op in ["sdiv", "udiv"] {
            assert_eq!(flags(op, &[]), Ok(()));
            assert_eq!(flags(op, &words(&["exact"])), Ok(()));
            for (bad, why) in [
                (words(&["exact", "exact"]), "exact more than once"),
                (words(&["exact", "exact", "exact"]), "exact more than once"),
                (words(&["nsw"]), "flag is exact, not nsw"),
                (words(&["exact", "nuw"]), "flag is exact, not nuw"),
                (words(&["EXACT"]), "not EXACT"),
                (vec![Attr::int(1)], "attributes are its flag exact, not 1"),
                (vec![Attr::Str("exact".into())], "attributes are its flag"),
                (vec![Attr::Sym("exact".into())], "attributes are its flag"),
                (
                    vec![Attr::App("exact".into(), vec![])],
                    "attributes are its flag",
                ),
            ] {
                let e = flags(op, &bad).unwrap_err();
                assert!(e.starts_with(op) && e.contains(why), "{op} {bad:?}: {e}");
            }
        }
        for op in ["srem", "urem"] {
            assert_eq!(flags(op, &[]), Ok(()));
            for bad in [
                words(&["exact"]),
                words(&["nsw"]),
                vec![Attr::int(0)],
                vec![Attr::App("exact".into(), vec![])],
            ] {
                let e = flags(op, &bad).unwrap_err();
                assert_eq!(e, format!("{op} takes no attributes"), "{bad:?}");
            }
        }
    }
}
