//! Conversions between float formats: `fpext` and `fptrunc`
//! (`decodeFpext` and `decodeFptrunc` in `lean/Fir/Core/FloatOpText.lean`,
//! `Op.Valid` in `lean/Fir/Core/Validation.lean`, `convertFloat` in
//! `lean/Fir/Core/FloatConvert.lean`; ADR-2026-11-09-1549).
//!
//! Each takes one value of a float type `float<e,m>` and defines one value
//! of another, `float<e',m'>`: the same number, rounded to nearest even
//! when the target does not hold it. `fpext` never rounds, so it has no
//! attribute; `fptrunc` rounds, so it carries `round(rne)`, the one mode M1
//! has (ADR-2026-11-11-1801). Any two formats decode, and validation says
//! which pairs each takes (the human's ruling of 2026-11-12 on #354):
//! `fpext` a target with at least as many exponent bits and as many
//! mantissa bits as the source, other than the source itself, so that it
//! holds every value of the source, and `fptrunc` every other pair of two
//! formats, `bf16` to `f16` and `f16` to `bf16` included. So every ordered
//! pair of two formats takes exactly one of them. Each is pure: it is never
//! UB, and it gives poison only for a poison operand.

use super::float_arith::decode_rounding;
use super::type_list;
use super::types::float_format;
use crate::effects::Effects;
use crate::registry::{OpContext, OpShape, OpSpec, OpTypes};

/// The conversions between float formats: `fpext` to a format that holds
/// every value of the source, and `fptrunc`, rounding, to any other.
pub const FLOAT_CONVERSIONS: [&str; 2] = ["fpext", "fptrunc"];

/// The formats `(e, m)` and `(e', m')` of an op that takes one value of
/// `float<e,m>` and defines one of `float<e',m'>`.
fn formats(op: &OpTypes<'_>) -> Option<((u32, u32), (u32, u32))> {
    let ([x], [r]) = (op.operands, op.results) else {
        return None;
    };
    Some((float_format(x)?, float_format(r)?))
}

/// Whether `float<e',m'>` holds every value of `float<e,m>`: it has at
/// least as many exponent bits and as many mantissa bits.
fn holds_every_value((e, m): (u32, u32), (e2, m2): (u32, u32)) -> bool {
    e <= e2 && m <= m2
}

/// `%d: f64 = fpext %f` and `%f: f32 = fptrunc round(rne) %d`.
pub(super) struct Convert(pub &'static str);

impl Convert {
    /// Whether the op is `fpext`, which does not round, rather than
    /// `fptrunc`.
    fn exact(&self) -> bool {
        self.0 == "fpext"
    }
}

impl OpSpec for Convert {
    fn name(&self) -> &str {
        self.0
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        decode_rounding(self.0, !self.exact(), op.attrs)?;
        match formats(op) {
            Some(_) => Ok(OpShape::default()),
            None => Err(format!(
                "{} takes one operand of a float type and defines one value of a float type, \
                 not {} -> {}",
                self.0,
                type_list(op.operands),
                type_list(op.results)
            )),
        }
    }

    fn check(&self, _cx: &OpContext<'_>, op: &OpTypes<'_>) -> Result<(), String> {
        let Some((from, to)) = formats(op) else {
            return Ok(());
        };
        let (valid, rule) = if self.exact() {
            (
                from != to && holds_every_value(from, to),
                "converts to another format that holds every value of the source, with at \
                 least as many exponent bits and mantissa bits",
            )
        } else {
            (
                !holds_every_value(from, to),
                "rounds into a format that cannot hold every value of the source, with fewer \
                 exponent bits or fewer mantissa bits",
            )
        };
        if valid {
            return Ok(());
        }
        Err(format!(
            "{} {rule}, not from {} to {}",
            self.0, op.operands[0], op.results[0]
        ))
    }

    /// Pure (`Core.Op.effects`).
    fn effects(&self, _op: &OpTypes<'_>) -> Effects {
        Effects::PURE
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialects::core::{float_type, int_type, ptr_type};
    use crate::{Attr, Module, Type};

    fn rne() -> Attr {
        Attr::App("round".into(), vec![Attr::word("rne")])
    }

    fn attrs(name: &str) -> Vec<Attr> {
        if name == "fpext" { vec![] } else { vec![rne()] }
    }

    fn types<'a>(attrs: &'a [Attr], operands: &'a [Type], results: &'a [Type]) -> OpTypes<'a> {
        OpTypes {
            attrs,
            operands,
            results,
        }
    }

    const FORMATS: [(u32, u32); 6] = [(5, 10), (8, 7), (8, 23), (11, 52), (15, 112), (2, 1)];

    #[test]
    fn any_two_formats_decode() {
        for name in FLOAT_CONVERSIONS {
            let a = attrs(name);
            for from in FORMATS {
                for to in FORMATS {
                    let (x, r) = ([float_type(from.0, from.1)], [float_type(to.0, to.1)]);
                    let got = Convert(name).decode(&types(&a, &x, &r));
                    assert_eq!(got, Ok(OpShape::default()), "{name} {from:?} {to:?}");
                }
            }
        }
    }

    #[test]
    fn every_other_pair_of_types_does_not_decode() {
        let (f32, f64, i32) = (float_type(8, 23), float_type(11, 52), int_type(32));
        for name in FLOAT_CONVERSIONS {
            let a = attrs(name);
            for (operands, results) in [
                (vec![i32.clone()], vec![f64.clone()]),
                (vec![f32.clone()], vec![i32.clone()]),
                (vec![ptr_type(0)], vec![f64.clone()]),
                (vec![f32.clone(), f32.clone()], vec![f64.clone()]),
                (vec![], vec![f64.clone()]),
                (vec![f32.clone()], vec![]),
                (vec![f32.clone()], vec![f64.clone(), f64.clone()]),
            ] {
                let e = Convert(name)
                    .decode(&types(&a, &operands, &results))
                    .unwrap_err();
                assert!(e.starts_with(&format!("{name} takes one operand")), "{e}");
            }
        }
    }

    #[test]
    fn fpext_has_no_attribute_and_fptrunc_needs_round_rne() {
        let (x, r) = ([float_type(8, 23)], [float_type(11, 52)]);
        let e = Convert("fpext")
            .decode(&types(&[rne()], &x, &r))
            .unwrap_err();
        assert!(e.starts_with("fpext"), "{e}");
        for bad in [
            vec![],
            vec![Attr::App("round".into(), vec![Attr::word("rtz")])],
            vec![rne(), rne()],
        ] {
            let e = Convert("fptrunc").decode(&types(&bad, &r, &x)).unwrap_err();
            assert!(e.starts_with("fptrunc") && e.contains("round(rne)"), "{e}");
        }
    }

    #[test]
    fn every_pair_of_two_formats_takes_exactly_one_op() {
        let m = Module::new();
        let symbols = m.symbols();
        let cx = OpContext {
            symbols: &symbols,
            func: "f",
            results: &[],
        };
        for from in FORMATS {
            for to in FORMATS {
                let (x, r) = ([float_type(from.0, from.1)], [float_type(to.0, to.1)]);
                let valid: Vec<&str> = FLOAT_CONVERSIONS
                    .into_iter()
                    .filter(|name| {
                        let a = attrs(name);
                        Convert(name).check(&cx, &types(&a, &x, &r)).is_ok()
                    })
                    .collect();
                let want: &[&str] = if from == to {
                    &[]
                } else if from.0 <= to.0 && from.1 <= to.1 {
                    &["fpext"]
                } else {
                    &["fptrunc"]
                };
                assert_eq!(valid, want, "{from:?} to {to:?}");
            }
        }
    }

    #[test]
    fn bf16_and_f16_take_fptrunc_both_ways() {
        let m = Module::new();
        let symbols = m.symbols();
        let cx = OpContext {
            symbols: &symbols,
            func: "f",
            results: &[],
        };
        let (f16, bf16) = ([float_type(5, 10)], [float_type(8, 7)]);
        for (x, r) in [(&f16, &bf16), (&bf16, &f16)] {
            let e = Convert("fpext").check(&cx, &types(&[], x, r)).unwrap_err();
            assert!(e.starts_with("fpext converts to another format"), "{e}");
            assert!(
                Convert("fptrunc")
                    .check(&cx, &types(&[rne()], x, r))
                    .is_ok()
            );
        }
        let f32 = [float_type(8, 23)];
        let e = Convert("fptrunc")
            .check(&cx, &types(&[rne()], &f32, &f32))
            .unwrap_err();
        assert!(e.ends_with("not from f32 to f32"), "{e}");
    }
}
