# Division lowers to one bare div or idiv of the op's own size

Status: accepted

## Context

[#18](https://github.com/pmatos/funk/issues/18) brings `sdiv`, `udiv`,
`srem` and `urem` to the x86-64 backend. In the spec
([`lean/Fir/Core/Div.lean`](../../lean/Fir/Core/Div.lean),
ADR-2026-10-30-0818), a zero or poison divisor is immediate UB, and so is
`sdiv` or `srem` by `-1` of the signed minimum or of poison. The human
ruled the poison dividend by `-1` UB on 2026-10-30, so that a backend
needs no guard. A broken `exact` gives poison. x86-64's `div` and `idiv`
trap on a zero divisor and on a quotient that does not fit. They divide at
four sizes: `%ax` by a byte, with the quotient in `%al` and the remainder
in `%ah`, and `%dx:%ax`, `%edx:%eax` and `%rdx:%rax` by a word, a long and
a quad. ADR-2026-10-30-1231 holds `iN` in the low `N` bits of 64, and says
that division first extends its operands to 64 bits.

## Decision

- **One instruction of the op's size.** `sdiv` and `srem` are one `idiv`,
  `udiv` and `urem` one `div`, of size `b`, `w`, `l` or `q` at `i8`,
  `i16`, `i32` and `i64`. The dividend is loaded into `%rax` and the
  divisor into `%rcx`. The instruction reads only their low `N` bits, so
  neither is extended to 64 bits. The dividend is widened into the high
  half that the instruction also reads: `cbtw`, `cwtd`, `cltd` or `cqto`
  for the signed ops, `movzbl %al, %eax` or `xorl %edx, %edx` for the
  unsigned ones. The quotient is in `%rax`; the remainder in `%rdx`, or in
  `%ah` at `i8`, which `movb %ah, %al` moves down.
- **`i1` divides as `i8`.** It has no instruction of its own, so both
  operands are extended to 64 bits with `width::extend`, by sign or by
  zero, and then divided as at `i8`. Its defined cases are `false` by
  `true` for `sdiv` and `srem`, and either value by `true` for `udiv` and
  `urem`.
- **No guard.** No code tests the divisor or the dividend. A zero divisor
  traps, and so does the signed minimum by `-1` at `i8` to `i64`. Both are
  immediate UB in the source, which any behaviour refines
  (ADR-2026-10-29-2008). At `i1`, `true` by `true` gives some value and
  does not trap, which UB allows too.
- **`exact` costs nothing.** `sdiv exact` and `udiv exact` lower as `sdiv`
  and `udiv`. Where `exact` is broken the source gives poison, and the
  quotient refines it (ADR-2026-10-30-2248).

This refines ADR-2026-10-30-1231 for division: a sized instruction reads
only the low `N` bits of its operands, so they need no extension, except
at `i1`.

## Alternatives

- **Extend both operands and use `idivq` or `divq` at every width.** It is
  one path, as ADR-2026-10-30-1231 first said. But below `i64` the signed
  minimum by `-1` no longer traps: the source's UB goes unseen where the
  hardware would show it.
- **A guard** that tests the divisor and branches to a trap or a fixed
  value. It costs a test and a branch on every division, for inputs on
  which the spec allows anything.

## Consequences

- Native tests run only inputs whose result is not UB in the spec. A run
  of one that is would trap.
- A division clobbers `%rax`, `%rcx` and `%rdx`. That is free while every
  value lives in a slot (ADR-2026-10-30-1230); a register allocator (M1)
  must treat them as clobbered.
- A later optimizer must not make a division run where the source would
  not, such as by hoisting it above the branch that tests its divisor:
  natively that adds a trap the source does not have.
