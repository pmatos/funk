//! The text of float constants on the shared cases of
//! `tests/dialects/float-text.cases`, which `lean/FirTest/FloatText.lean`
//! reads too: `scripts/harness/float_text.py`, an exact-rational reference,
//! computed every case, so Rust, Lean and the reference agree on each
//! spelling and on how each decimal rounds (ADR-2026-11-11-1438).

use funk_ir::dialects::core::{float_constant, read_float, spell_float};

const CASES: &str = include_str!("../../../tests/dialects/float-text.cases");

fn format(f: &str) -> (u32, u32) {
    let (e, m) = f.split_once(',').expect("a format is e,m");
    (e.parse().expect("e"), m.parse().expect("m"))
}

fn bits(b: &str) -> u128 {
    u128::from_str_radix(b.strip_prefix("0x").expect("bits after 0x"), 16).expect("hexadecimal")
}

#[test]
fn every_shared_case_holds() {
    let (_, body) = CASES.split_once("---\n").expect("the cases follow ---");
    let mut n = 0;
    for line in body.lines() {
        let words: Vec<&str> = line.split(' ').collect();
        match words.as_slice() {
            ["spell", f, b, text] => {
                let (e, m) = format(f);
                assert_eq!(spell_float(e, m, bits(b)), *text, "{line}");
                assert_eq!(float_constant(e, m, text), Ok(Some(bits(b))), "{line}");
            }
            ["read", f, text, b] => {
                let (e, m) = format(f);
                assert_eq!(read_float(e, m, text), Some(bits(b)), "{line}");
                assert!(float_constant(e, m, text).is_err(), "{line}");
            }
            ["reject", f, text] => {
                let (e, m) = format(f);
                assert_eq!(read_float(e, m, text), None, "{line}");
                assert!(float_constant(e, m, text).is_err(), "{line}");
            }
            _ => panic!("not a case: {line}"),
        }
        n += 1;
    }
    assert!(n > 400, "{n} cases");
}
