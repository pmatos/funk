//! Float arithmetic: `fadd`, `fsub`, `fmul`, `fdiv`, `frem`, `fmod`,
//! `fneg`, `fabs`, `sqrt` and `fma` (`decodeFBin`, `decodeFUnary` and
//! `decodeFma` in `lean/Fir/Core/FloatOpText.lean`; ADR-2026-11-09-1549).
//!
//! Each op takes values of one float type and defines one value of it:
//! two operands for `fadd`, `fsub`, `fmul`, `fdiv`, `frem` and `fmod`, one
//! for `fneg`, `fabs` and `sqrt`, and three for `fma`. Each op that rounds
//! has one attribute, its rounding mode `round(MODE)`, with MODE one of
//! the `rounding` module's `ROUNDING_MODES`.
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
use super::rounding::{check_rounding, decode_rounding};
use super::type_list;
use super::types::float_format;
use crate::Type;
use crate::effects::Effects;
use crate::registry::{OpContext, OpShape, OpSpec, OpTypes};

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
    use crate::dialects::core::float_type;

    #[test]
    fn every_op_that_rounds_decodes_every_mode_and_validates_only_rne() {
        for op in FloatArith::all().filter(|op| op.rounds) {
            let f = float_type(8, 23);
            super::super::rounding::assert_every_mode_decodes_and_only_rne_validates(
                &op,
                &vec![f.clone(); op.operands],
                &[f],
            );
        }
    }
}
