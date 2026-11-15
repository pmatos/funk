//! The rounding mode of a float op that rounds (`RoundingMode` in
//! `lean/Fir/Core/Rounding.lean`, `decodeRound` in
//! `lean/Fir/Core/RoundingText.lean`, its rule in `Op.Valid`;
//! ADR-2026-11-11-1801).
//!
//! An op that rounds writes its mode as one attribute, `round(MODE)`, with
//! MODE one of [`ROUNDING_MODES`], IEEE 754's five rounding-direction
//! attributes. Every mode decodes, and validation accepts only `round(rne)`,
//! round to nearest even: the other modes are hooks in the format (the
//! human's ruling of 2026-11-15 on #229). An op that does not round takes no
//! attribute.

use crate::Attr;

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
    let modes = || ROUNDING_MODES.map(|m| format!("round({m})")).join(", ");
    match (rounds, attrs) {
        (true, [a]) if round_mode(a).is_some() => Ok(()),
        (true, [Attr::App(head, _)]) if head == "round" => Err(format!(
            "{op}'s rounding mode is one of {}, not {}",
            modes(),
            attrs[0]
        )),
        (true, []) => Err(format!(
            "{op} has one attribute, its rounding mode, one of {}, and has none",
            modes()
        )),
        (true, [a]) => Err(format!(
            "{op}'s attribute is its rounding mode, one of {}, not {a}",
            modes()
        )),
        (true, _) => Err(format!(
            "{op} has one attribute, its rounding mode, one of {}, not {}",
            modes(),
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

/// Checks that `spec`, an op that rounds, decodes at the given types with
/// every mode and that its check accepts `rne` alone.
#[cfg(test)]
pub(super) fn assert_every_mode_decodes_and_only_rne_validates(
    spec: &dyn crate::registry::OpSpec,
    operands: &[crate::Type],
    results: &[crate::Type],
) {
    use crate::registry::{OpContext, OpShape, OpTypes};
    let symbols = crate::SymbolTable::of(&[]);
    let cx = OpContext {
        symbols: &symbols,
        func: "f",
        results: &[],
    };
    for mode in ROUNDING_MODES {
        let attrs = [Attr::App("round".into(), vec![Attr::word(mode)])];
        let op = OpTypes {
            attrs: &attrs,
            operands,
            results,
        };
        assert_eq!(spec.decode(&op), Ok(OpShape::default()), "{mode}");
        match spec.check(&cx, &op) {
            Ok(()) => assert_eq!(mode, "rne"),
            Err(e) => assert!(
                mode != "rne" && e.contains(&format!("not round({mode})")),
                "{e}"
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialects::core::FLOAT_ARITH_OPS;

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
