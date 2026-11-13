# Current decisions: the x86-64 backend, lowering floats

This page continues [x86-64-backend-lowering.md](x86-64-backend-lowering.md).
It says what holds today for how the naive backend lowers the float ops at
`f32` and `f64`: comparison, arithmetic, the remainders, bit casts and the
conversions. It is the record: when this page and an ADR disagree, the page
wins, and the ADR is fixed or deleted (ADR-2026-11-09-1610). Each lowering
here builds on spill-everything, and native code holds no poison
(ADR-2026-10-30-2248). An `f16`, `bf16` or `f128` value is reported where it
is defined (ADR-2026-11-09-1549).

## Float comparison

`fcmp` loads its operands with `movss` or `movsd` into `%xmm0` and `%xmm1`,
compares them with `ucomiss` or `ucomisd`, and reads the flags with one
`setCC`, or two for `oeq` and `une`. `oeq` also needs the parity flag clear, and
`une` accepts it set, since an unordered pair sets it.

## Float arithmetic

The backend lowers the float arithmetic at `f32` and `f64` with SSE2, which every
x86-64 has, and the remainders with the x87 unit, which every x86-64 has too. `fadd`, `fsub`, `fmul`, `fdiv` and `sqrt` are one instruction
each, `addss`, `subss`, `mulss`, `divss`, `sqrtss` or their `sd` forms, on
`%xmm0` and the second operand's slot. MXCSR keeps its default mode, round to
nearest even. Nothing sets its flush-to-zero or denormals-are-zero bits, so
subnormals are honoured. `fneg` and `fabs` flip or clear the sign bit in `%rax`
with `btcq` or `btrq`, which is IEEE 754's negate and abs, also on a NaN, and
refines fir's any NaN (ADR-2026-11-09-1549). A NaN result is whatever the
instruction or routine gives.

SSE2 has no fused multiply-add, and FMA3 is not in every x86-64. So `fma` loads
its operands into `%xmm0` to `%xmm2` and calls `__funk_rt_fmaf` or
`__funk_rt_fma`, hand-written in `crates/funk-x86-64/src/lower/fma.s`, which
`lower::module` appends once as it appends `div128.s`. Each is a System V
function of three floats that uses only caller-saved registers and 16 bytes of
stack, within the 24 bytes that the stack figure counts for a helper.

At `f32` the product is exact in `f64`. The routine rounds the sum to odd in
`f64`, toward zero with the last bit set when it was inexact, and then to
nearest even in `f32`. Rounding to odd with two more bits rounds once (Boldo
and Melquiond, 2008). MXCSR is restored after. At `f64` it computes
`a * b + c` exactly in 128-bit integers and rounds once, subnormals and
overflow included. NaN and infinite operands, and zeros, take SSE's
`a * b + c` or `a * b`, which is exact or correctly signed there.
`crates/funk/tests/float_arith.rs` checks every op against the host's IEEE 754
arithmetic.

Rejected: FMA3's `vfmadd`, since a program that uses it fails on an x86-64
without FMA3, and the default stays baseline x86-64 (the human ruled on
2026-11-12 that CPU extensions come in through a `--cpu` flag in M2; see
[the roadmap](../roadmap.md));
`fma` from the C library, since most modules link none; and double-double
arithmetic at `f64`, which loses exactness near overflow and among subnormals.

### The remainders

SSE has no remainder. So `frem` and `fmod` load their operands into `%xmm0` and
`%xmm1` and call `__funk_rt_fremf`, `__funk_rt_frem`, `__funk_rt_fmodf` or
`__funk_rt_fmod`, hand-written in `crates/funk-x86-64/src/lower/frem.s`, which
`lower::module` appends once as it appends `fma.s` (#310). Each routine moves
its operands through one pushed word onto the x87 stack and runs `fprem1`, IEEE
754's remainder with the quotient rounded to nearest even, for `frem`, or
`fprem`, C's `fmod` with the quotient truncated, for `fmod`. Each reduces the
exponent by 32 to 63 bits at a time, as the processor chooses, and sets C2
while it is partial, so the routine loops until C2 is clear: 34 to 66 times for
the largest `f64` by the smallest subnormal. Both are exact whatever the x87
precision control says, and the result is exact in the format, so the store to
`f32` or `f64` is exact.
They give a NaN on `y = 0` or an infinite `x`, `x` itself on an infinite `y`,
and a zero with `x`'s sign, as the spec does. A routine uses `%rax`, `%xmm0`,
`%xmm1` and the x87 stack, which it leaves empty, and 16 bytes of stack.
`crates/funk/tests/float_arith.rs` checks both against the host's arithmetic on
the hard values and on random operands, operands far apart and quotient ties
among them.

Rejected: `fmod` and `remainder` from the C library, since most modules link
none; and a routine on the integer unit that shifts and subtracts the
mantissas, which is longer, slower on far-apart operands, and needs its own
proof of the rounding of the quotient, where `fprem1` is IEEE 754's own.

## Bit casts

`bitcast` between `f32` and `i32`, or `f64` and `i64`, copies its operand's
slot to its result's through `%rax`. A float is its bits in a slot, as an
integer is, and the bits of either above its width are unspecified, so no
instruction converts: no SSE instruction runs, and a NaN's sign and payload,
a signalling NaN's included, come through as they are, as fir's rule asks
(ADR-2026-11-09-1549). An `f16`, `bf16` or `f128` side is reported where it is
defined, as for every float op. `crates/funk/tests/float_bitcast.rs` checks
that both directions keep every bit of the hard values of `floats.rs`, NaNs
included. Rejected:
`movd` or `movq` between a general register and an SSE register, which moves
the same bits through one more register.

## Conversions from integers

`sitofp` and `uitofp` from `i1` to `i128` to `f32` or `f64` convert with
SSE2's `cvtsi2ssq` or `cvtsi2sdq`, which convert a signed 64-bit integer,
rounded as MXCSR says; its default mode is round to nearest even, as
`round(rne)` asks (#241). An operand of at most 64 bits is extended to 64, by
sign for `sitofp` and by zero for `uitofp`, since the bits above its width are
unspecified ([x86-64-backend.md](x86-64-backend.md#values-and-widths)), and
converted with one instruction.

An unsigned `i64` of `2^63` or more is halved, with the bit it drops ORed into
its lowest bit, converted and added to itself. The halved value has 63 bits,
more than the 24 or 53 of the result and the round bit below them, so its
lowest bit records only whether anything below was set, and the conversion
rounds once; doubling is exact. An `i128` takes the magnitude of a negative
`sitofp` operand, converts it as unsigned, and flips the result's sign bit. An
unsigned value below `2^64` converts as above. Any other is shifted left until
the high half's top bit is set; the high half, with its lowest bit ORed with
whether the low half has a bit set, is halved and converted as above, and the
result is multiplied by the power of two the shifts took off. That product is
exact unless it overflows `f32`, which only an unsigned `i128` near `2^128`
does, and then it is the infinity that rounding to nearest gives. The code is
inline, at local labels, and calls no routine.
`crates/funk/tests/float_int_to_float.rs` checks each path against the host's
conversion on boundary values, ties and random values, with operands narrower
than 64 bits truncated from `i64` values whose high bits are random. Rejected:
a routine of a runtime helper for `i128`, as for `fma`, which the lowering
cannot choose from the op alone, since an op names its operand but not its
type.

## Conversions between formats

`fpext` from `f32` to `f64` is SSE2's `cvtss2sd`, which is exact, and `fptrunc`
from `f64` to `f32` is `cvtsd2ss`, which rounds as MXCSR's default mode does,
to nearest even, as `round(rne)` asks (#241). Each reads its operand's slot,
keeps the sign of a zero and an infinity, honours subnormals, and gives an
infinity or a zero of its sign past either end of `f32`; a NaN gives a quiet
NaN, which fir's rule allows. Every other pair has an `f16`, `bf16` or `f128`
side, reported where it is defined. `crates/funk/tests/float_convert.rs`
checks both against the host's `as` on the edges and on random bits.

## Conversions to integers

`fptosi` and `fptoui` from `f32` or `f64` to `i1` up to `i128` truncate toward
zero, and give poison for an integer that `iN` does not hold, an infinity or a
NaN (#241). Native code holds no poison, so any value refines it
(ADR-2026-10-30-2248): the code must give the exact integer only where the
source gives one, and checks a range only where the instruction's own range is
narrower than `iN`'s.

SSE2's `cvttss2siq` and `cvttsd2siq` truncate toward zero into a signed 64-bit
integer, exactly from `-2^63` up to below `2^63`, and give `-2^63` otherwise.
That is all of `fptosi` up to `i64` and of `fptoui` below `i64`: the result's
low `N` bits are the integer
([x86-64-backend.md](x86-64-backend.md#values-and-widths)). `fptoui` to `i64`
compares the operand with `2^63` by `ucomiss` or `ucomisd`; one at or above it
has `2^63` subtracted first, which is exact there, and its top bit set back
after the conversion. An `i128` has no instruction: an `f32` goes to `f64` with
`cvtss2sd`, which is exact, and the code shifts the `f64`'s mantissa, with its
hidden bit, by its exponent into `%rdx:%rax`, right below `2^52` and left
above, across the halves with `shldq` as a shift at `i128` does. A number
below `1` gives `0`, and `fptosi` negates the pair for a negative operand. An
exponent past the width shifts by a count that the processor masks, and gives
some value. The code is inline, at local labels, and calls no routine.
`crates/funk/tests/float_to_int.rs` checks each path against the host's `trunc`
on the edges of every width and on random values, and that every case the
source makes poison prints a value of the type. Rejected: a routine of a
runtime helper for `i128`, as `fma` has, where a short inline sequence does;
and saturating out-of-range values, as Rust's `as` does, which costs compares
that the source does not ask for.
