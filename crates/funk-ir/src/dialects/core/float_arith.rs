//! Float arithmetic: `fadd`, `fsub`, `fmul`, `fdiv`, `frem`, `fmod`,
//! `fneg`, `fabs`, `sqrt` and `fma` (`decodeFBin`, `decodeFUnary` and
//! `decodeFma` in `lean/Fir/Core/FloatOpText.lean`; ADR-2026-11-09-1549).
//!
//! Each op takes values of one float type and defines one value of it:
//! two operands for `fadd`, `fsub`, `fmul`, `fdiv`, `frem` and `fmod`, one
//! for `fneg`, `fabs` and `sqrt`, and three for `fma`. Each op that rounds
//! has one attribute, `round(rne)`, round to nearest even, the one mode M1
//! has. `frem`, `fmod`, `fneg` and `fabs` do not round, since their result
//! is exact, and have none (ADR-2026-11-11-1801). So `fadd %a, %b`,
//! `fadd round(rtz) %a, %b` and `frem round(rne) %a, %b` do not decode.
//! Each may carry the fast-math flags before its other attributes (the
//! `fast_math` module): validation rejects the reserved words `contract`
//! and `reassoc`. Without `nnan` and `ninf` each is pure: it is never UB, a
//! NaN result is a defined value, and it gives poison only for a poison
//! operand.

use super::fast_math::{self, Flags};
use super::type_list;
use super::types::float_format;
use crate::effects::Effects;
use crate::registry::{OpContext, OpShape, OpSpec, OpTypes};
use crate::{Attr, Type};

/// The float ops of arithmetic: each name, its number of operands, and
/// whether it rounds, so that it carries `round(rne)`.
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

/// Whether `a` is `round(rne)`.
fn is_round_rne(a: &Attr) -> bool {
    match a {
        Attr::App(head, args) if head == "round" => {
            matches!(args.as_slice(), [Attr::Word(m)] if m == "rne")
        }
        _ => false,
    }
}

/// Checks that the attributes of the float op `op` are `round(rne)` when
/// it rounds and none when it does not, or says why they are not.
pub(super) fn decode_rounding(op: &str, rounds: bool, attrs: &[Attr]) -> Result<(), String> {
    match (rounds, attrs) {
        (true, [a]) if is_round_rne(a) => Ok(()),
        (true, [Attr::App(head, _)]) if head == "round" => Err(format!(
            "{op} rounds to nearest even, round(rne), the one rounding mode, not {}",
            attrs[0]
        )),
        (true, []) => Err(format!(
            "{op} has one attribute, its rounding mode round(rne), and has none"
        )),
        (true, [a]) => Err(format!(
            "{op}'s attribute is its rounding mode round(rne), not {a}"
        )),
        (true, _) => Err(format!(
            "{op} has one attribute, its rounding mode round(rne), not {}",
            attrs.len()
        )),
        (false, []) => Ok(()),
        (false, _) => Err(format!("{op} does not round and takes no attributes")),
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

    /// No reserved word among the flags (`Op.Valid`).
    fn check(&self, _cx: &OpContext<'_>, op: &OpTypes<'_>) -> Result<(), String> {
        Flags::decode(self.name, op.attrs).map_or(Ok(()), |f| f.check(self.name))
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
        for (rounds, bad, why) in [
            (true, vec![], "and has none"),
            (true, vec![round("rtz")], "not round(rtz)"),
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
}
