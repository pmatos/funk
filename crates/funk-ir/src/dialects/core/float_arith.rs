//! Float arithmetic: `fadd`, `fsub`, `fmul`, `fdiv`, `frem`, `fmod`,
//! `fneg`, `fabs`, `sqrt` and `fma` (`decodeFBin`, `decodeFUnary` and
//! `decodeFma` in `lean/Fir/Core/FloatOpText.lean`; ADR-2026-11-09-1549).
//!
//! Each op takes values of one float type and defines one value of it:
//! two operands for `fadd`, `fsub`, `fmul`, `fdiv`, `frem` and `fmod`, one
//! for `fneg`, `fabs` and `sqrt`, and three for `fma`. Each op that rounds
//! has one attribute, its rounding mode `round(MODE)`, with MODE one of
//! [`ROUNDING_MODES`] (`decodeRound` in `lean/Fir/Core/RoundingText.lean`).
//! `frem`, `fmod`, `fneg` and `fabs` do not round, since their result is
//! exact, and have none (ADR-2026-11-11-1801). So `fadd %a, %b`,
//! `fadd round(up) %a, %b` and `frem round(rne) %a, %b` do not decode.
//! Validation accepts only `round(rne)`, round to nearest even: the other
//! modes are hooks in the format, so `fadd round(rtz) %a, %b` decodes and
//! fails validation (the human's ruling of 2026-11-15 on #229). Each may
//! carry the fast-math flags before its other attributes (the `fast_math`
//! module): validation rejects the reserved words `contract` and
//! `reassoc`. Without `nnan` and `ninf` each is pure: it is never UB, a
//! NaN result is a defined value, and it gives poison only for a poison
//! operand.

use super::fast_math::{self, Flags};
use super::type_list;
use super::types::float_format;
use crate::effects::Effects;
use crate::registry::{OpContext, OpShape, OpSpec, OpTypes};
use crate::{Attr, Type};

/// The float ops of arithmetic: each name, its number of operands, and
/// whether it rounds, so that it carries a rounding mode.
pub const FLOAT_ARITH_OPS: [(&str, usize, bool); 10] = [
    ("fadd", 2, true),
    ("fsub", 2, true),
    ("fmul", 2, true),
    ("fdiv", 2, true),
    ("frem", 2, false),
    ("fmod", 2, false),
    ("fneg", 1, false),
    ("fabs", 1, false),
    ("sqrt", 1, true),
    ("fma", 3, true),
];

/// The rounding modes, as words (`RoundingMode.word`): IEEE 754's five
/// rounding-direction attributes. Validation accepts only `rne`.
pub const ROUNDING_MODES: [&str; 5] = ["rne", "rna", "rtp", "rtn", "rtz"];

/// The mode of `a` when it is `round(MODE)` with MODE one of
/// [`ROUNDING_MODES`].
fn round_mode(a: &Attr) -> Option<&str> {
    let Attr::App(head, args) = a else {
        return None;
    };
    match args.as_slice() {
        [Attr::Word(m)] if head == "round" && ROUNDING_MODES.contains(&m.as_str()) => Some(m),
        _ => None,
    }
}

/// Checks that the attributes of the float op `op` are one rounding mode,
/// `round(MODE)`, when it rounds and none when it does not, or says why
/// they are not.
pub(super) fn decode_rounding(op: &str, rounds: bool, attrs: &[Attr]) -> Result<(), String> {
    match (rounds, attrs) {
        (true, [a]) if round_mode(a).is_some() => Ok(()),
        (true, [Attr::App(head, _)]) if head == "round" => Err(format!(
            "{op}'s rounding mode is one of {}, not {}",
            ROUNDING_MODES.map(|m| format!("round({m})")).join(", "),
            attrs[0]
        )),
        (true, []) => Err(format!(
            "{op} has one attribute, its rounding mode round(MODE), and has none"
        )),
        (true, [a]) => Err(format!(
            "{op}'s attribute is its rounding mode round(MODE), not {a}"
        )),
        (true, _) => Err(format!(
            "{op} has one attribute, its rounding mode round(MODE), not {}",
            attrs.len()
        )),
        (false, []) => Ok(()),
        (false, _) => Err(format!("{op} does not round and takes no attributes")),
    }
}

/// Checks that the float op `op`, which rounds, rounds to nearest even,
/// `round(rne)`, the one mode M1 accepts (`Op.Valid`).
pub(super) fn check_rounding(op: &str, attrs: &[Attr]) -> Result<(), String> {
    match attrs.iter().find_map(round_mode) {
        Some(m) if m != "rne" => Err(format!(
            "{op} rounds to nearest even in M1, round(rne), not round({m}): \
             the other rounding modes are hooks"
        )),
        _ => Ok(()),
    }
}

/// The format of an op whose `n` operands and one result are of one float
/// type (`floatOpFormat`).
fn op_format(n: usize, operands: &[Type], results: &[Type]) -> Option<(u32, u32)> {
    let [r] = results else { return None };
    let f = float_format(r)?;
    (operands.len() == n && operands.iter().all(|t| float_format(t) == Some(f))).then_some(f)
}

/// One of [`FLOAT_ARITH_OPS`]: `%s: f32 = fadd round(rne) %a, %b`,
/// `%n: f32 = fneg %a`, `%f: f64 = fma round(rne) %a, %b, %c`.
pub(super) struct FloatArith {
    pub name: &'static str,
    pub operands: usize,
    pub rounds: bool,
}

impl FloatArith {
    /// Every op of [`FLOAT_ARITH_OPS`].
    pub(super) fn all() -> impl Iterator<Item = FloatArith> {
        FLOAT_ARITH_OPS
            .into_iter()
            .map(|(name, operands, rounds)| FloatArith {
                name,
                operands,
                rounds,
            })
    }
}

impl OpSpec for FloatArith {
    fn name(&self) -> &str {
        self.name
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        let flags = Flags::decode(self.name, op.attrs)?;
        decode_rounding(self.name, self.rounds, flags.rest).map_err(|e| flags.after(e))?;
        if op_format(self.operands, op.operands, op.results).is_some() {
            return Ok(OpShape::default());
        }
        let what = match self.operands {
            1 => "one operand",
            2 => "two operands",
            _ => "three operands",
        };
        Err(format!(
            "{} takes {what} of one float type and defines one value of that type, not {} -> {}",
            self.name,
            type_list(op.operands),
            type_list(op.results)
        ))
    }

    /// No reserved word among the flags, and the mode `rne` when it rounds
    /// (`Op.Valid`).
    fn check(&self, _cx: &OpContext<'_>, op: &OpTypes<'_>) -> Result<(), String> {
        let Ok(flags) = Flags::decode(self.name, op.attrs) else {
            return Ok(());
        };
        flags.check(self.name)?;
        check_rounding(self.name, flags.rest)
    }

    /// Never UB, and a poison result only for a poison operand, or with
    /// `nnan` or `ninf` (`Core.Op.effects`).
    fn effects(&self, op: &OpTypes<'_>) -> Effects {
        fast_math::effects_of(op.attrs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn round(mode: &str) -> Attr {
        Attr::App("round".into(), vec![Attr::word(mode)])
    }

    #[test]
    fn rounding_decodes_as_decode_fbin_reads_it() {
        for (op, _, rounds) in FLOAT_ARITH_OPS {
            let want = if rounds { vec![round("rne")] } else { vec![] };
            assert_eq!(decode_rounding(op, rounds, &want), Ok(()), "{op}");
        }
        for mode in ROUNDING_MODES {
            assert_eq!(
                decode_rounding("fadd", true, &[round(mode)]),
                Ok(()),
                "{mode}"
            );
        }
        for (rounds, bad, why) in [
            (true, vec![], "and has none"),
            (true, vec![round("up")], "not round(up)"),
            (true, vec![round("RNE")], "not round(RNE)"),
            (true, vec![round("rne"), round("rne")], "not 2"),
            (true, vec![Attr::word("rne")], "not rne"),
            (true, vec![Attr::App("round".into(), vec![])], "not round()"),
            (
                true,
                vec![Attr::App(
                    "round".into(),
                    vec![Attr::word("rne"), Attr::word("rne")],
                )],
                "not round(rne, rne)",
            ),
            (false, vec![round("rne")], "takes no attributes"),
        ] {
            let e = decode_rounding("fadd", rounds, &bad).unwrap_err();
            assert!(e.starts_with("fadd") && e.contains(why), "{bad:?}: {e}");
        }
    }

    #[test]
    fn validation_accepts_only_round_rne() {
        assert_eq!(check_rounding("fadd", &[round("rne")]), Ok(()));
        assert_eq!(check_rounding("frem", &[]), Ok(()));
        for mode in ROUNDING_MODES.into_iter().filter(|m| *m != "rne") {
            let e = check_rounding("sqrt", &[Attr::word("nnan"), round(mode)]).unwrap_err();
            assert!(
                e.starts_with("sqrt rounds to nearest even")
                    && e.contains(&format!("round({mode})")),
                "{e}"
            );
        }
    }
}
