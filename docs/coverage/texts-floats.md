# What the corpus texts test: float arithmetic and conversions

This page continues [texts.md](texts.md): it lists the texts of the fir
test corpus that test the float arithmetic, the remainders and the
conversions, in the order their tickets added them. Paths are relative to
`tests/fir/`, but for those of the harness, under `scripts/harness/`.

The texts of #229's fourth stage also use the float arithmetic `fadd`,
`fsub`, `fmul`, `fdiv`, `fneg`, `fabs`, `sqrt` and `fma`
([ADR-2026-11-09-1549](../adrs/2026-11-09-1549-floating-point-is-strict-ieee-over-generic-formats.md),
[ADR-2026-11-11-1801](../adrs/2026-11-11-1801-a-rounding-op-is-written-with-round-rne.md)).
`float-binary-T` runs `fadd`, `fsub`, `fmul` and `fdiv`, and
`float-unary-fma-T` runs `fneg`, `fabs`, `sqrt` and `fma`, at `T`, one of
`f16`, `bf16`, `f32`, `f64` and `f128`, on the hard inputs: results
halfway between two floats, subnormals, `-0`, overflow to infinity and
NaN operands, `fsub` and `fdiv` in both operand orders, and a poison
operand. `scripts/harness/float_arith_cases.py` writes them, with each
expected result that `scripts/harness/float_ref.py` computes
([testing-and-harness-floats.md](../decisions/testing-and-harness-floats.md#the-arithmetic-corpus)).
A result that is not a NaN is differential at `f32` and `f64` and
interpreter-only at every format; a NaN result is interpreter-only, with
a choice that names the NaN, until #219. `reject/float-arith.toml` holds
the texts of these ops that do not decode, such as `fadd` without
`round(rne)` or with `round(rtz)`, and one at a format that validation
rejects.

The texts of #241's first stage also use the bit cast `bitcast`
([ADR-2026-11-09-1549](../adrs/2026-11-09-1549-floating-point-is-strict-ieee-over-generic-formats.md)).
`float-bitcast-T` casts a value of `T`, one of `f16`, `bf16`, `f32`,
`f64` and `f128`, to the integer of its width and back, on zeros of both
signs, subnormals, the smallest normal, one, the largest finite values,
infinities and NaNs with payloads and either sign, and on poison. Each
result is its operand's bits, so every case is differential at `f32` and
`f64`, NaNs included, and interpreter-only at every format.
`scripts/harness/float_bitcast_cases.py` writes them
([testing-and-harness-floats.md](../decisions/testing-and-harness-floats.md#the-bit-cast-corpus)).
`reject/float-bitcast.toml` holds the bit casts that do not decode, such
as an integer of another width, two floats or two integers, and an
attribute, and two at formats that validation rejects.

The texts of #310 also use the remainders `frem`, IEEE 754's, and `fmod`,
C's ([semantics-floats.md](../decisions/semantics-floats.md#the-remainders)).
`float-rem-T` runs both at each `T`, on the hard inputs of
`scripts/harness/float_rem_cases.py`: quotients halfway between two
integers, subnormals, `-0`, operands far apart, infinities and NaN
operands, each in both operand orders, and a poison operand, as
`float_arith_cases.py` writes them. `reject/float-arith.toml` holds
`frem round(rne)`, which does not decode, since a remainder does not
round.

The texts of #241's third stage use the conversions from integers to floats,
`sitofp` and `uitofp`, with `round(rne)`
([ADR-2026-11-09-1549](../adrs/2026-11-09-1549-floating-point-is-strict-ieee-over-generic-formats.md)).
`float-sitofp-T` and `float-uitofp-T` convert an integer of each width that
the backend lowers, `i1` to `i128`, to `T`, one of `f16`, `bf16`, `f32`, `f64`
and `f128`, and
`float-itofp-odd` converts `i7` and `i33` to each of them. The cases are the
boundary integers of each width, signed and unsigned, the integers next to the
format's precision, the integers halfway between two floats and next to them,
the integers on either side of overflow, and poison. A conversion never gives
a NaN, so every case of a lowered width is differential at `f32` and `f64`,
and every case is interpreter-only with its expected result.
`scripts/harness/float_itofp_cases.py` writes them
([testing-and-harness-floats.md](../decisions/testing-and-harness-floats.md#the-integer-to-float-corpus)).
`reject/float-itofp.toml` holds the conversions that do not decode, such as
one without `round(rne)`, with `round(rtz)` or a flag, from a float or to an
integer, and two at a width or format that validation rejects.

The texts of #241's second stage use the conversions between float formats,
`fpext`, with no attribute, and `fptrunc`, with `round(rne)`
([semantics-floats-conversions.md](../decisions/semantics-floats-conversions.md#the-conversions)).
`float-OP-S-T` converts from `S` to `T` with the op that the pair takes, for
each ordered pair of two of `f16`, `bf16`, `f32`, `f64` and `f128`: `fpext`
where `T` has at least as many exponent bits and mantissa bits as `S`, and
`fptrunc` otherwise, as from `bf16` to `f16` and back. The cases are the
source's zeros, subnormals, largest finite value and infinities, the
target's largest finite value and smallest subnormal where the source holds
them, the values halfway past them and between two values of the target with
their neighbours, three NaNs and poison. A NaN gives any NaN, so its case is
interpreter-only with a choice; every other case is interpreter-only with its
expected result, and differential too in `float-fpext-f32-f64` and
`float-fptrunc-f64-f32`. `scripts/harness/float_convert_cases.py` writes them
([testing-and-harness-floats.md](../decisions/testing-and-harness-floats.md#the-format-conversion-corpus)).
`reject/float-convert.toml` holds the conversions that do not decode, such as
`fpext round(rne)`, `fptrunc` without `round(rne)` and either from or to an
integer, and those that validation rejects: a pair that takes the other op,
`bf16` to `f16` and `f16` to `bf16` as `fpext` among them, a format to
itself, and a format that validation rejects everywhere.

The texts of #241's fourth stage use the conversions from floats to integers,
`fptosi` and `fptoui`, with no attribute: both truncate toward zero
([semantics-floats-conversions.md](../decisions/semantics-floats-conversions.md#the-conversions)).
`float-fptosi-T` and `float-fptoui-T` convert `T`, one of `f16`, `bf16`,
`f32`, `f64` and `f128`, to an integer of each width that the backend lowers,
`i1` to `i128`, and `float-fptosi-odd` and `float-fptoui-odd` convert each of them to `i7` and
`i33`. The cases are the zeros, the smallest subnormal, small fractions such
as `2.7`, the largest finite values, infinities and NaNs, each of either sign,
the floats on either side of each end of the width's range, and poison. An
integer out of range, an infinity or a NaN gives poison. A conversion
chooses nothing, so every case of a lowered width is differential at `f32` and
`f64`, where native code may give any value for poison, and every case is
interpreter-only with its expected result.
`scripts/harness/float_fptoi_cases.py` writes them
([testing-and-harness-floats.md](../decisions/testing-and-harness-floats.md#the-float-to-integer-corpus)).
`reject/float-fptoi.toml` holds the conversions that do not decode, such as
`fptosi round(rne)`, `fptoui round(rtz)`, a flag, from an integer or to a
float, and two at a width or format that validation rejects.
