//! Width changes: `zext`, `sext` and `trunc` (`decodeCast` in
//! `lean/Fir/Core/Text.lean`, `Op.Valid` in `lean/Fir/Core/Validation.lean`).
//!
//! Each op takes one `iM` and defines one `iN`, with no attributes. Any `M`
//! and `N` decode, so a text whose op changes to the same width, or in the
//! wrong direction, parses. Validation then rejects it: `zext` and `sext`
//! strictly widen, with `M < N`, and `trunc` strictly narrows, with `N < M`
//! (ADR-2026-10-30-0818).

use super::type_list;
use super::types::int_width;
use crate::registry::{OpContext, OpShape, OpSpec, OpTypes};

/// The width changes, each as the text names it.
pub const WIDTH_CHANGES: [&str; 3] = ["zext", "sext", "trunc"];

/// The widths `M` and `N` of an op that takes one `iM` and defines one
/// `iN`.
fn cast_widths(op: &OpTypes<'_>) -> Option<(u32, u32)> {
    let ([x], [r]) = (op.operands, op.results) else {
        return None;
    };
    Some((int_width(x)?, int_width(r)?))
}

/// `%w: iN = zext %x`, and `sext` and `trunc` likewise.
pub(super) struct Cast(pub &'static str);

impl Cast {
    /// Whether the op widens, as `zext` and `sext` do, rather than narrows.
    fn widens(&self) -> bool {
        self.0 != "trunc"
    }
}

impl OpSpec for Cast {
    fn name(&self) -> &str {
        self.0
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        if !op.attrs.is_empty() {
            return Err(format!("{} takes no attributes", self.0));
        }
        match cast_widths(op) {
            Some(_) => Ok(OpShape::default()),
            None => Err(format!(
                "{} takes one operand of an integer type and defines one value of an \
                 integer type, not {} -> {}",
                self.0,
                type_list(op.operands),
                type_list(op.results)
            )),
        }
    }

    fn check(&self, _cx: &OpContext<'_>, op: &OpTypes<'_>) -> Result<(), String> {
        let Some((m, n)) = cast_widths(op) else {
            return Ok(());
        };
        let (valid, rule) = if self.widens() {
            (m < n, "strictly widens, from iM to iN with M < N")
        } else {
            (n < m, "strictly narrows, from iM to iN with N < M")
        };
        if valid {
            return Ok(());
        }
        Err(format!("{} {rule}, not from i{m} to i{n}", self.0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialects::core::int_type;
    use crate::{Attr, Module, Type};

    fn types<'a>(attrs: &'a [Attr], operands: &'a [Type], results: &'a [Type]) -> OpTypes<'a> {
        OpTypes {
            attrs,
            operands,
            results,
        }
    }

    #[test]
    fn any_pair_of_widths_decodes_and_nothing_else_does() {
        let (i8, i64, ptr) = (int_type(8), int_type(64), Type::word("ptr"));
        for op in WIDTH_CHANGES.map(Cast) {
            for (from, to) in [(&i8, &i8), (&i8, &i64), (&i64, &i8)] {
                let t = types(&[], std::slice::from_ref(from), std::slice::from_ref(to));
                assert_eq!(op.decode(&t), Ok(OpShape::default()), "{}", op.0);
            }
            let one = std::slice::from_ref(&i8);
            for (operands, results) in [
                (&[i8.clone(), i8.clone()][..], one),
                (&[], one),
                (one, &[]),
                (one, &[i8.clone(), i8.clone()][..]),
                (std::slice::from_ref(&ptr), one),
                (one, std::slice::from_ref(&ptr)),
            ] {
                let e = op.decode(&types(&[], operands, results)).unwrap_err();
                assert!(e.contains("takes one operand of an integer type"), "{e}");
            }
            for a in [Attr::word("nuw"), Attr::int(1)] {
                let e = op.decode(&types(&[a], one, one)).unwrap_err();
                assert_eq!(e, format!("{} takes no attributes", op.0));
            }
        }
    }

    #[test]
    fn zext_and_sext_strictly_widen_and_trunc_strictly_narrows() {
        let m = Module::new();
        let symbols = m.symbols();
        let cx = OpContext {
            symbols: &symbols,
            func: "f",
            results: &[],
        };
        for op in WIDTH_CHANGES.map(Cast) {
            for (from, to) in [(1, 1), (8, 8), (1, 8), (8, 32), (32, 8), (64, 1)] {
                let (x, r) = ([int_type(from)], [int_type(to)]);
                let valid = if op.0 == "trunc" {
                    to < from
                } else {
                    from < to
                };
                let got = op.check(&cx, &types(&[], &x, &r));
                assert_eq!(got.is_ok(), valid, "{} from i{from} to i{to}", op.0);
                if let Err(e) = got {
                    assert!(e.ends_with(&format!("not from i{from} to i{to}")), "{e}");
                }
            }
        }
    }
}
