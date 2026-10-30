//! Integer arithmetic: `add`, `sub` and `mul` with their flags (`Op.decode`
//! and `decodeWrap` in `lean/Fir/Core/Text.lean`).
//!
//! Each op takes two `iN` and defines one `iN`. Its attributes are its
//! flags, `nuw` and `nsw`: none, one, or both, and then `nuw` before `nsw`.
//! Each flag has one spelling and is written at most once, so `add nsw nuw`,
//! `add nuw nuw` and `add exact` do not decode. A broken flag gives poison,
//! not an error, so validation has no rule for these ops beyond their
//! signature (`Op.Valid` in `lean/Fir/Core/Validation.lean`).

use super::type_list;
use super::types::int_width;
use crate::registry::{OpShape, OpSpec, OpTypes};
use crate::{Attr, Type};

/// The flags that `add`, `sub` and `mul` may have, each set as the text
/// writes it (`decodeWrap`): none, `nuw`, `nsw`, or both with `nuw` first.
pub const WRAP_FLAG_SETS: [&[&str]; 4] = [&[], &["nuw"], &["nsw"], &["nuw", "nsw"]];

/// The width `N` of an op that takes two `iN` and defines one `iN`
/// (`binWidth`).
fn bin_width(operands: &[Type], results: &[Type]) -> Option<u32> {
    let [a, b] = operands else { return None };
    let [r] = results else { return None };
    let w = int_width(a)?;
    (int_width(b)? == w && int_width(r)? == w).then_some(w)
}

/// Checks that the attributes of the op `op` are one of
/// [`WRAP_FLAG_SETS`], or says why they are not.
fn decode_flags(op: &str, attrs: &[Attr]) -> Result<(), String> {
    let mut words = Vec::with_capacity(attrs.len());
    for a in attrs {
        match a {
            Attr::Word(w) if w == "nuw" || w == "nsw" => words.push(w.as_str()),
            Attr::Word(w) => return Err(format!("{op}'s flags are nuw and nsw, not {w}")),
            _ => {
                return Err(format!(
                    "{op}'s attributes are its flags nuw and nsw, not {a}"
                ));
            }
        }
    }
    if WRAP_FLAG_SETS.contains(&words.as_slice()) {
        return Ok(());
    }
    let twice = |w: &&&str| words.iter().filter(|v| v == w).count() > 1;
    Err(match words.iter().find(twice) {
        Some(w) => format!("{op} has the flag {w} more than once"),
        None => format!("{op} writes its flags in one order, nuw before nsw"),
    })
}

/// `%r: iN = add %a, %b`, and `sub` and `mul` likewise, each with the
/// flags `nuw` and `nsw`.
pub(super) struct Wrap(pub &'static str);

impl OpSpec for Wrap {
    fn name(&self) -> &str {
        self.0
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        decode_flags(self.0, op.attrs)?;
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

    fn flags(words: &[&str]) -> Result<(), String> {
        let attrs: Vec<Attr> = words.iter().map(|w| Attr::word(*w)).collect();
        decode_flags("add", &attrs)
    }

    #[test]
    fn flags_decode_as_decode_wrap_reads_them() {
        for ok in WRAP_FLAG_SETS {
            assert_eq!(flags(ok), Ok(()), "{ok:?}");
        }
        for (bad, why) in [
            (&["nsw", "nuw"][..], "nuw before nsw"),
            (&["nuw", "nuw"], "nuw more than once"),
            (&["nsw", "nsw"], "nsw more than once"),
            (&["nuw", "nsw", "nsw"], "nsw more than once"),
            (&["nuw", "nsw", "nuw"], "nuw more than once"),
            (&["exact"], "not exact"),
            (&["nuw", "exact"], "not exact"),
            (&["NSW"], "not NSW"),
        ] {
            let e = flags(bad).unwrap_err();
            assert!(e.contains(why), "{bad:?}: {e}");
        }
        let e = decode_flags("mul", &[Attr::int(1)]).unwrap_err();
        assert!(e.contains("mul's attributes are its flags"), "{e}");
    }
}
