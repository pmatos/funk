//! Comparison and selection: `icmp` and `select` (`Op.decode` in
//! `lean/Fir/Core/Text.lean`).
//!
//! `icmp` has one attribute, its predicate, written as LLVM writes it:
//! `%lt: i1 = icmp slt %a, %b`. It takes two `iN` and defines one `i1`. So
//! `icmp %a, %b`, `icmp slt sgt`, `icmp lt`, `icmp slt nsw` and the old
//! spelling `icmp.slt`, which names no op, do not decode. `select` takes an
//! `i1` condition and two `iN` and defines one `iN`, with no attributes.
//! Validation has no rule for either op beyond its signature (`Op.Valid` in
//! `lean/Fir/Core/Validation.lean`).

use super::type_list;
use super::types::int_width;
use crate::Attr;
use crate::registry::{OpShape, OpSpec, OpTypes};

/// The predicates of `icmp`, in the spec's order (`Pred.all`).
pub const PREDICATES: [&str; 10] = [
    "eq", "ne", "slt", "sle", "sgt", "sge", "ult", "ule", "ugt", "uge",
];

/// Checks that the attributes of `icmp` are one predicate, or says why
/// they are not.
fn decode_predicate(attrs: &[Attr]) -> Result<(), String> {
    let p = match attrs {
        [p] => p,
        [] => return Err("icmp has one attribute, its predicate, and has none".into()),
        _ => {
            return Err(format!(
                "icmp has one attribute, its predicate, not {}",
                attrs.len()
            ));
        }
    };
    match p {
        Attr::Word(w) if PREDICATES.contains(&w.as_str()) => Ok(()),
        Attr::Word(w) => Err(format!(
            "icmp's predicate is one of {}, not {w}",
            PREDICATES.join(", ")
        )),
        _ => Err(format!("icmp's attribute is its predicate, not {p}")),
    }
}

/// `%lt: i1 = icmp slt %a, %b`, with any of [`PREDICATES`].
pub(super) struct Icmp;

impl OpSpec for Icmp {
    fn name(&self) -> &str {
        "icmp"
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        decode_predicate(op.attrs)?;
        let well_typed = match (op.operands, op.results) {
            ([a, b], [r]) => {
                int_width(r) == Some(1) && int_width(a).is_some_and(|w| int_width(b) == Some(w))
            }
            _ => false,
        };
        if well_typed {
            return Ok(OpShape::default());
        }
        Err(format!(
            "icmp takes two operands of one integer type and defines one i1, not {} -> {}",
            type_list(op.operands),
            type_list(op.results)
        ))
    }
}

/// `%r: iN = select %c, %a, %b`.
pub(super) struct Select;

impl OpSpec for Select {
    fn name(&self) -> &str {
        "select"
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        if !op.attrs.is_empty() {
            return Err("select takes no attributes".into());
        }
        let well_typed = match (op.operands, op.results) {
            ([c, a, b], [r]) => {
                int_width(c) == Some(1)
                    && int_width(a)
                        .is_some_and(|w| int_width(b) == Some(w) && int_width(r) == Some(w))
            }
            _ => false,
        };
        if well_typed {
            return Ok(OpShape::default());
        }
        Err(format!(
            "select takes an i1 condition and two operands of one integer type, and \
             defines one value of that type, not {} -> {}",
            type_list(op.operands),
            type_list(op.results)
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn words(ws: &[&str]) -> Vec<Attr> {
        ws.iter().map(|w| Attr::word(*w)).collect()
    }

    #[test]
    fn predicates_decode_as_op_decode_reads_them() {
        for p in PREDICATES {
            assert_eq!(decode_predicate(&words(&[p])), Ok(()), "{p}");
        }
        for (bad, why) in [
            (words(&[]), "and has none"),
            (words(&["slt", "slt"]), "not 2"),
            (words(&["slt", "sgt"]), "not 2"),
            (words(&["nsw", "slt"]), "not 2"),
            (words(&["lt"]), "not lt"),
            (words(&["SLT"]), "not SLT"),
            (words(&["true"]), "not true"),
            (words(&["nsw"]), "not nsw"),
            (vec![Attr::int(1)], "attribute is its predicate, not 1"),
            (vec![Attr::Str("slt".into())], "attribute is its predicate"),
            (vec![Attr::Sym("slt".into())], "attribute is its predicate"),
            (
                vec![Attr::App("slt".into(), vec![])],
                "attribute is its predicate",
            ),
        ] {
            let e = decode_predicate(&bad).unwrap_err();
            assert!(e.starts_with("icmp") && e.contains(why), "{bad:?}: {e}");
        }
    }
}
