//! Tests of the spelling of float constants against Rust's own `f32` and
//! `f64`, whose `{:e}` writes the shortest decimal that reads back and
//! whose `parse` rounds to nearest even. Of two shortest decimals equally
//! near the value, Rust may write either, and fir the one with an even last
//! digit. The shared cases of `tests/dialects/float-text.cases` check every
//! format.

use super::*;
use crate::generate::Rng;

/// Rust's shortest decimal of `x`, in the layout of a float constant.
fn rust_spelling(x: f64) -> String {
    let sci = format!("{x:e}");
    let (mantissa, exp) = sci.split_once('e').expect("{:e} writes an exponent");
    let exp: i64 = exp.parse().expect("an integer exponent");
    let neg = mantissa.starts_with('-');
    let digits: String = mantissa.chars().filter(char::is_ascii_digit).collect();
    let c = Big::from_digits(&digits);
    layout(neg, &c, exp - (digits.len() as i64 - 1))
}

#[test]
fn spellings_are_rusts_shortest_decimals() {
    let mut rng = Rng::new(1438);
    for _ in 0..3000 {
        let b = rng.next_u64();
        let x = f64::from_bits(b);
        let s = spell_float(11, 52, u128::from(b));
        if x.is_finite() {
            if x != 0.0 {
                same_or_even_tie(&s, &rust_spelling(x));
            }
            assert_eq!(s.parse::<f64>().map(f64::to_bits), Ok(b), "{s}");
        } else {
            assert_eq!(s, format!("0x{b:016x}"));
        }
        assert_eq!(float_constant(11, 52, &s), Ok(Some(u128::from(b))));
        let b32 = b as u32;
        let x32 = f32::from_bits(b32);
        let s32 = spell_float(8, 23, u128::from(b32));
        if x32.is_finite() {
            assert_eq!(s32.parse::<f32>().map(f32::to_bits), Ok(b32), "{s32}");
            if x32 != 0.0 {
                same_or_even_tie(&s32, &rust_spelling_f32(x32));
            }
        }
        assert_eq!(float_constant(8, 23, &s32), Ok(Some(u128::from(b32))));
    }
}

/// fir's spelling `ours` is Rust's `theirs`, or as short, ending in an even
/// digit where Rust's ends in an odd one: the other of a tie.
fn same_or_even_tie(ours: &str, theirs: &str) {
    if ours == theirs {
        return;
    }
    let digits = |s: &str| -> Vec<u8> {
        let m = s.split('e').next().unwrap_or(s);
        m.bytes().filter(u8::is_ascii_digit).collect()
    };
    let (a, b) = (digits(ours), digits(theirs));
    assert_eq!(a.len(), b.len(), "{ours} and {theirs}");
    assert!(a.last().is_some_and(|d| d % 2 == 0), "{ours} and {theirs}");
}

fn rust_spelling_f32(x: f32) -> String {
    let sci = format!("{x:e}");
    let (mantissa, exp) = sci.split_once('e').expect("{:e} writes an exponent");
    let exp: i64 = exp.parse().expect("an integer exponent");
    let neg = mantissa.starts_with('-');
    let digits: String = mantissa.chars().filter(char::is_ascii_digit).collect();
    layout(
        neg,
        &Big::from_digits(&digits),
        exp - (digits.len() as i64 - 1),
    )
}

#[test]
fn reading_rounds_to_nearest_even_as_rust_does() {
    let mut rng = Rng::new(229);
    for _ in 0..3000 {
        let digits: String = (0..1 + rng.below(30))
            .map(|_| char::from(b'0' + rng.below(10) as u8))
            .collect();
        let exp = rng.below(700) as i64 - 350;
        let d = Big::from_digits(&digits);
        let text = format!("{digits}e{exp}");
        let want = text.parse::<f64>().expect("a decimal").to_bits();
        assert_eq!(
            Format { e: 11, m: 52 }.read(false, &d, exp),
            u128::from(want),
            "{text}"
        );
        let want32 = text.parse::<f32>().expect("a decimal").to_bits();
        assert_eq!(
            Format { e: 8, m: 23 }.read(false, &d, exp),
            u128::from(want32),
            "{text}"
        );
    }
}

#[test]
fn only_the_one_spelling_decodes() {
    assert_eq!(float_constant(8, 23, "1.0"), Ok(Some(0x3f80_0000)));
    assert_eq!(float_constant(8, 23, "0x7fc00000"), Ok(Some(0x7fc0_0000)));
    for bad in [
        "1.00",
        "1.0e0",
        "0x3f800000",
        "0x7fc0000",
        "1.0e39",
        "1.0e10000",
        "10000000000000000.0",
    ] {
        assert!(float_constant(8, 23, bad).is_err(), "{bad}");
    }
    assert!(float_constant(16, 3, "0.0").is_err());
    assert_eq!(float_constant(16, 3, "0x00000"), Ok(Some(0)));
    assert_eq!(float_constant(1, 1, "0x7"), Ok(Some(7)));
    assert!(float_constant(1, 1, "0x8").is_err());
    let wide = format!("0x{}", "0".repeat(250));
    assert_eq!(float_constant(900, 99, &wide), Ok(None));
    assert_eq!(spell_float(5, 10, 0x7bff), "65500.0");
    assert_eq!(spell_float(15, 112, 1), "6.0e-4966");
}
