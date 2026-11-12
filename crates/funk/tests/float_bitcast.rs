//! `bitcast` runs natively between `f32` and `i32` and between `f64` and
//! `i64` (#241, `docs/decisions/x86-64-backend-lowering.md#bit-casts`).
//! Each result is checked against the host's `to_bits` and `from_bits`, on
//! zeros of both signs, subnormals, ones, the largest finite values,
//! infinities and NaNs, quiet and signalling, with payloads and either
//! sign: a bit cast keeps every bit, a NaN's too. The floats pass and
//! return in SSE registers and the integers in general registers, so the
//! cases also check that a bit cast moves its value from one to the other.

mod common;

use common::{build, expect, func, module};

/// The hard bit patterns of `f32`.
const F32: [u32; 14] = [
    0x0000_0000, // +0
    0x8000_0000, // -0
    0x0000_0001, // the smallest subnormal
    0x8000_0001,
    0x007f_ffff, // the largest subnormal
    0x3f80_0000, // 1.0
    0xbf80_0000, // -1.0
    0x7f7f_ffff, // the largest finite value
    0x7f80_0000, // +inf
    0xff80_0000, // -inf
    0x7fc0_0000, // the quiet NaN
    0xffc0_0001, // a quiet NaN with its sign set and a payload
    0x7f80_0001, // a signalling NaN
    0xffff_ffff,
];

/// The hard bit patterns of `f64`.
const F64: [u64; 13] = [
    0,
    0x8000_0000_0000_0000,
    1,
    0x000f_ffff_ffff_ffff,
    0x3ff0_0000_0000_0000,
    0xbff0_0000_0000_0000,
    0x7fef_ffff_ffff_ffff,
    0x7ff0_0000_0000_0000,
    0xfff0_0000_0000_0000,
    0x7ff8_0000_0000_0000,
    0xfff0_0000_0000_0001,
    0x7ff4_0000_0000_0000,
    0xffff_ffff_ffff_ffff,
];

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
        let bits = (f32::from_bits(b).to_bits() as i32).to_string();
        expect(&exe, &["@bits", &x], &[&bits]);
        expect(&exe, &["@float", &x], &[&bits]);
        expect(&exe, &["@both", &x], &[&bits]);
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
        let bits = (f64::from_bits(b).to_bits() as i64).to_string();
        expect(&exe, &["@bits", &x], &[&bits]);
        expect(&exe, &["@float", &x], &[&bits]);
        expect(&exe, &["@both", &x], &[&bits]);
        let flipped = ((b ^ (1 << 63)) as i64).to_string();
        expect(&exe, &["@flip", &x], &[&flipped]);
    }
}
