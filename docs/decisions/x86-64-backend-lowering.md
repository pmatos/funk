# Current decisions: the x86-64 backend, lowering `i128`, division and floats

This page continues x86-64-backend.md. It says what holds today for how the
naive backend lowers `i128` values, the divisions and the float arithmetic. It only summarizes the
ADRs it cites (ADR-2026-11-09-1610). When this page and an ADR disagree, the
page has a bug.

## Lowering `i128`

An op at `i128` loads each operand's low half into `%rax` and its high half into
`%rdx`. It computes and stores both halves. `add` and `sub` carry between the
halves with `adcq` and `sbbq`. `mul` is `mulq` of the low halves. The low 64
bits of the two cross products are added into the high half. `and`, `or` and `xor` apply to each half.

A shift uses `shldq` or `shrdq` and then two `cmovneq` for amounts from 64 to
127, with no branch. `icmp eq` and `ne` `xorq` the halves and `orq` the two.
Other predicates are `cmpq` and `sbbq`, then `setl`, `setge`, `setb` or `setae`.
`select` uses one `cmovzq` per half.

`zext` and `sext` extend the operand to 64 bits and fill the high half. `trunc`
copies the low half. A branch passes an `i128` as two copies of its parallel
move. Poison is not tracked per half. `freeze` copies both halves into its own
two slots (ADR-2026-11-03-010730).

## Division

A zero or poison divisor is immediate UB in the source. So is `sdiv` or `srem`
by `-1` of the signed minimum or of poison (ADR-2026-10-30-0818).

Below `i128`, `sdiv` and `srem` are one `idiv`, and `udiv` and `urem` one `div`,
of the op's own size. The dividend goes in `%rax` and the divisor in `%rcx`. The
dividend is widened into the high half that the instruction reads. `i1` divides
as `i8`, after both operands are extended (ADR-2026-10-31-0050).

No code tests the divisor or the dividend. A zero divisor traps, and so does
the signed minimum by `-1` at `i8` to `i64`. `exact` costs nothing. Native tests
run only inputs whose result is not UB (ADR-2026-10-31-0050).

At `i128`, each op calls one of `__funk_rt_sdiv128`, `__funk_rt_udiv128`,
`__funk_rt_srem128` or `__funk_rt_urem128`. These are hand-written assembly in
`crates/funk-x86-64/src/lower/div128.s`. `lower::module` appends that file once
to a module's assembly when a function of it divides at `i128`. So `OUTPUT.o`
stands alone. No routine is `.globl`, so two such objects link into one C
program. No fir function's symbol starts with `__funk_rt_`
(ADR-2026-11-03-0414).

Each routine is a System V function `__int128 f(__int128 a, __int128 b)`. They
use only caller-saved registers and leave `%rsp` as they found it. So nothing
is saved around the call. A `b` below `2^64` takes two `divq`, and a larger one
takes 64 steps of restoring division. A zero divisor traps in the first `divq`.
There is no guard (ADR-2026-11-03-0415).

## Float arithmetic

The backend lowers the float arithmetic at `f32` and `f64` with SSE2 only, which
every x86-64 has. `fadd`, `fsub`, `fmul`, `fdiv` and `sqrt` are one instruction
each, `addss` to `sqrtss` or their `sd` forms, on `%xmm0` and the second
operand's slot. MXCSR keeps its default mode, round to nearest even, and no
flush-to-zero, so subnormals are honoured. `fneg` and `fabs` flip or clear the
sign bit in `%rax` with `btcq` or `btrq`, which is IEEE 754's negate and abs and
refines fir's any NaN (ADR-2026-11-11-1802).

SSE2 has no fused multiply-add, and FMA3 is not in every x86-64. So `fma` calls
`__funk_rt_fmaf` or `__funk_rt_fma`, hand-written in
`crates/funk-x86-64/src/lower/fma.s`, which `lower::module` appends once as it
appends `div128.s`. At `f32` the routine rounds the sum to odd in `f64` and then
to `f32`, which rounds once. At `f64` it computes `a * b + c` exactly in 128-bit
integers and rounds once. Each routine uses only caller-saved registers and 16
bytes of stack (ADR-2026-11-11-1802).
