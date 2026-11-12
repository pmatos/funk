//! `bitcast` runs natively between `f32` and `i32` and between `f64` and
//! `i64` (#241, `docs/decisions/x86-64-backend-lowering.md#bit-casts`).
//! A bit cast keeps every bit, so each result is its operand's bits, a
//! NaN's too, on the hard values that `floats.rs` uses: zeros of both
//! signs, subnormals, ones, the largest finite values, infinities and NaNs,
//! quiet and signalling, with payloads and either sign. The floats pass and
//! return in SSE registers and the integers in general registers, so the
//! cases also check that a bit cast moves its value from one to the other.

mod common;

use common::{F32, F64, build, expect, func, module};

/// The module of the bit casts at the float type `t` and the integer type
/// `i`: `@bits` and `@float` cast each way, `@both` casts there and back,
/// and `@flip` flips the sign bit of a float's bits with `xor`.
fn bitcasts(t: &str, i: &str, sign: &str) -> String {
    module(&[
        func(
            "bits",
            &format!("%a: {t}"),
            i,
            &[&format!("%r: {i} = bitcast %a"), "ret %r"],
        ),
        func(
            "float",
            &format!("%a: {i}"),
            t,
            &[&format!("%r: {t} = bitcast %a"), "ret %r"],
        ),
        func(
            "both",
            &format!("%a: {t}"),
            t,
            &[
                &format!("%b: {i} = bitcast %a"),
                &format!("%r: {t} = bitcast %b"),
                "ret %r",
            ],
        ),
        func(
            "flip",
            &format!("%a: {t}"),
            i,
            &[
                &format!("%s: {i} = const {sign}"),
                &format!("%b: {i} = bitcast %a"),
                &format!("%r: {i} = xor %b, %s"),
                "ret %r",
            ],
        ),
    ])
}

#[test]
fn bitcast_keeps_every_bit_at_f32() {
    let exe = build("bitcast-f32", &bitcasts("f32", "i32", "-2147483648"));
    for b in F32 {
        let x = (b as i32).to_string();
        expect(&exe, &["@bits", &x], &[&x]);
        expect(&exe, &["@float", &x], &[&x]);
        expect(&exe, &["@both", &x], &[&x]);
        let flipped = ((b ^ 0x8000_0000) as i32).to_string();
        expect(&exe, &["@flip", &x], &[&flipped]);
    }
}

#[test]
fn bitcast_keeps_every_bit_at_f64() {
    let sign = i64::MIN.to_string();
    let exe = build("bitcast-f64", &bitcasts("f64", "i64", &sign));
    for b in F64 {
        let x = (b as i64).to_string();
        expect(&exe, &["@bits", &x], &[&x]);
        expect(&exe, &["@float", &x], &[&x]);
        expect(&exe, &["@both", &x], &[&x]);
        let flipped = ((b ^ (1 << 63)) as i64).to_string();
        expect(&exe, &["@flip", &x], &[&flipped]);
    }
}
