//! The fast-math flags of the float ops (`FastMath`, `splitFlags` in
//! `lean/Fir/Core/FloatOpText.lean`; ADR-2026-11-09-1549).
//!
//! `fcmp` and every float op of arithmetic may carry the flags `nnan`,
//! `ninf` and `nsz` before their other attributes, each as a word, at most
//! once, in the fixed order [`FAST_MATH_FLAGS`]:
//! `%s: f32 = fadd nnan nsz round(rne) %a, %b` and
//! `%c: i1 = fcmp ninf olt %a, %b`. A flag out of order, written twice, or
//! after the op's other attributes does not decode.
//!
//! `nnan` and `ninf` make a NaN or an infinite operand or result poison,
//! so an op with either may produce poison. `nsz` makes the sign of a zero
//! result a choice, a defined value, so it keeps the op pure. `contract`
//! and `reassoc` are reserved words: they decode, and validation rejects
//! them, since M2's optimizer decides them (`Op.Valid` in
//! `lean/Fir/Core/Validation.lean`).

use crate::Attr;
use crate::effects::Effects;

/// The flags in their fixed order: the three that an op may carry, then
/// the two reserved words (`FastMath.attrs`).
pub const FAST_MATH_FLAGS: [&str; 5] = ["nnan", "ninf", "nsz", "contract", "reassoc"];

/// The reserved words among [`FAST_MATH_FLAGS`].
const RESERVED: [&str; 2] = ["contract", "reassoc"];

/// Whether `a` is the word of one of [`FAST_MATH_FLAGS`].
fn is_flag(a: &Attr) -> bool {
    matches!(a, Attr::Word(w) if FAST_MATH_FLAGS.contains(&w.as_str()))
}

/// The flags of a float op, read from the front of its attributes, and the
/// attributes after them (`splitFlags`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) struct Flags<'a> {
    /// Which of [`FAST_MATH_FLAGS`] the op carries, in their order.
    set: [bool; 5],
    /// The op's other attributes.
    pub rest: &'a [Attr],
}

impl<'a> Flags<'a> {
    /// Takes the flags from the front of `attrs`, each when it is the next
    /// attribute, in the order of [`FAST_MATH_FLAGS`]. The op's own
    /// attributes must come after them and hold no flag, or the op does
    /// not decode: `op` names it in the reason.
    pub fn decode(op: &str, attrs: &'a [Attr]) -> Result<Flags<'a>, String> {
        let mut set = [false; 5];
        let mut rest = attrs;
        for (i, flag) in FAST_MATH_FLAGS.iter().enumerate() {
            if let [Attr::Word(w), tail @ ..] = rest
                && w == flag
            {
                set[i] = true;
                rest = tail;
            }
        }
        if rest.iter().any(is_flag) {
            return Err(format!(
                "{op}'s fast-math flags come first, each at most once, in the order {}",
                FAST_MATH_FLAGS.join(", ")
            ));
        }
        Ok(Flags { set, rest })
    }

    /// The effects of a float op with these flags: it may produce poison
    /// with `nnan` or `ninf`, and is pure otherwise (`Core.Op.effects`).
    pub fn effects(&self) -> Effects {
        Effects {
            may_poison: self.set[0] || self.set[1],
            ..Effects::PURE
        }
    }

    /// Checks that the op carries no reserved word, or says why it may not
    /// (`Op.Valid`).
    pub fn check(&self, op: &str) -> Result<(), String> {
        let reserved: Vec<&str> = FAST_MATH_FLAGS
            .iter()
            .zip(self.set)
            .filter(|(f, on)| *on && RESERVED.contains(f))
            .map(|(f, _)| *f)
            .collect();
        if reserved.is_empty() {
            return Ok(());
        }
        Err(format!(
            "{op} carries {}: contract and reassoc are reserved words, which M2's optimizer decides",
            reserved.join(" and ")
        ))
    }
}

/// The effects of a float op whose attributes are `attrs`: those of its
/// flags, or pure when they do not decode.
pub(super) fn effects_of(attrs: &[Attr]) -> Effects {
    Flags::decode("", attrs).map_or(Effects::PURE, |f| f.effects())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn words(ws: &[&str]) -> Vec<Attr> {
        ws.iter().map(|w| Attr::word(*w)).collect()
    }

    fn round() -> Attr {
        Attr::App("round".into(), vec![Attr::word("rne")])
    }

    #[test]
    fn flags_decode_as_split_flags_reads_them() {
        let attrs = [words(&["nnan", "nsz"]), vec![round()]].concat();
        let f = Flags::decode("fadd", &attrs).unwrap();
        assert_eq!(f.set, [true, false, true, false, false]);
        assert_eq!(f.rest, &[round()]);
        let all = words(&FAST_MATH_FLAGS);
        assert_eq!(Flags::decode("fneg", &all).unwrap().set, [true; 5]);
        let olt = words(&["olt"]);
        assert_eq!(Flags::decode("fcmp", &olt).unwrap().set, [false; 5]);
        for bad in [
            vec!["nsz", "nnan"],
            vec!["nnan", "nnan"],
            vec!["reassoc", "contract"],
            vec!["olt", "ninf"],
        ] {
            let e = Flags::decode("fcmp", &words(&bad)).unwrap_err();
            assert!(
                e.starts_with("fcmp's fast-math flags come first"),
                "{bad:?}: {e}"
            );
        }
        let after = [vec![round()], words(&["nnan"])].concat();
        assert!(Flags::decode("fadd", &after).is_err());
    }

    #[test]
    fn nnan_and_ninf_may_produce_poison_and_nsz_keeps_an_op_pure() {
        for (ws, poison) in [
            (vec![], false),
            (vec!["nnan"], true),
            (vec!["ninf"], true),
            (vec!["nsz"], false),
            (vec!["contract", "reassoc"], false),
            (vec!["nnan", "ninf", "nsz"], true),
        ] {
            assert_eq!(effects_of(&words(&ws)).may_poison, poison, "{ws:?}");
        }
    }

    #[test]
    fn validation_rejects_the_reserved_words() {
        let ok = words(&["nnan", "ninf", "nsz"]);
        assert_eq!(Flags::decode("fadd", &ok).unwrap().check("fadd"), Ok(()));
        let one = words(&["nnan", "contract"]);
        let e = Flags::decode("fadd", &one)
            .unwrap()
            .check("fadd")
            .unwrap_err();
        assert!(
            e.starts_with("fadd carries contract:") && e.contains("M2"),
            "{e}"
        );
        let both = words(&["contract", "reassoc"]);
        let e = Flags::decode("fcmp", &both)
            .unwrap()
            .check("fcmp")
            .unwrap_err();
        assert!(e.starts_with("fcmp carries contract and reassoc:"), "{e}");
    }
}
