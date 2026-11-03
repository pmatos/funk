# The i128 division routines are System V functions that clobber only caller-saved registers, and the stack figure counts them

Status: accepted

## Context

ADR-2026-11-03-0414 puts the routines that divide at `i128` in the
module's object file. A call of one must leave its caller's state as the
caller needs it.

- Every value of a funk function lives in its slots below `%rbp`. No
  value stays in a register from one op to the next, and a function saves
  only `%rbp` (ADR-2026-10-30-1230). `%rsp` is 16-byte aligned between
  ops.
- A funk function passes an `i128` in two registers, its low half first,
  and returns one in `%rdx:%rax` (ADR-2026-11-03-0108).
- In the spec, a zero or poison divisor is immediate UB, and so are
  `sdiv` and `srem` of the signed minimum or of poison by `-1`
  (ADR-2026-10-30-0818). A broken `exact` gives poison. Below `i128` each
  op is one bare `div` or `idiv`, with no guard (ADR-2026-10-31-0050).
- `divq` divides 128 bits by 64, and traps on a zero divisor and on a
  quotient that does not fit in 64 bits.
- A built executable's stack figure covers every call
  (ADR-2026-11-02-1132).

## Decision

- **System V.** Each of `__funk_rt_sdiv128`, `__funk_rt_udiv128`,
  `__funk_rt_srem128` and `__funk_rt_urem128` is a System V function
  `__int128 f(__int128 a, __int128 b)`: `a` in `%rdi` (low half) and
  `%rsi` (high half), `b` in `%rdx` and `%rcx`, and the result in `%rax`
  and `%rdx`. The routines use only `%rax`, `%rcx`, `%rdx`, `%rsi`,
  `%rdi` and `%r8` to `%r11`, which System V lets a callee clobber, and
  return with `%rsp` as they found it. They never touch `%rbx`, `%rbp`
  or `%r12` to `%r15`.
- **What the caller keeps.** A division at `i128` loads `a` and `b` from
  their slots into those registers, `call`s its op's routine, and stores
  `%rax` and `%rdx` into its result's slots. Its function keeps nothing in
  a register across the op, and the routine keeps `%rbp`, through which
  every slot is reached, and `%rsp`; so nothing is saved around the call.
  It is a plain `call`, as the wrapper's calls of `__funk_rt_arg` are: the
  call emitter `abi::call` is for calls of funk functions, by their fir
  names (ADR-2026-11-02-1428).
- **How it divides.** `__funk_rt_udivmod128` gives the unsigned quotient
  and remainder. When `b` is below `2^64`, two `divq` divide by one 64-bit
  digit: `a`'s high half by `b`, then that remainder and `a`'s low half by
  `b`. Otherwise the quotient fits in 64 bits, and restoring division
  takes the 64 bits of `a`'s low half, one a step, into a remainder that
  starts as `a`'s high half, subtracting `b` from it whenever it reaches
  `b`. The signed routines divide the magnitudes and negate the quotient
  when the signs differ, and the remainder when `a` is negative.
- **No guard.** A zero divisor traps in the first `divq`, as at `i64`.
  `sdiv` and `srem` of the signed minimum by `-1` give some value. Both
  are immediate UB in the source, which any behaviour refines.
  `sdiv exact` and `udiv exact` call the routines of `sdiv` and `udiv`:
  where `exact` is broken the quotient refines poison
  (ADR-2026-10-30-2248).
- **The figure counts the routines.** A routine uses at most 24 bytes
  below its caller's `%rsp`: its return address, the sign that
  `__funk_rt_sdiv128` and `__funk_rt_srem128` push, and their call of
  `__funk_rt_udivmod128` or `__funk_rt_magnitudes`. `entry/stack.rs`
  counts a function that divides at `i128` as making a call that pushes
  no argument and needs `HELPER_STACK`, 24 bytes.

This refines ADR-2026-10-31-0050, whose bare `div` or `idiv` stops at
`i64`, and ADR-2026-11-02-1132, whose figure now covers the helper's
calls too.

## Alternatives

- **Hacker's Delight's estimate** for `b` of `2^64` or more: one `divq` of
  normalized operands and a correction, in place of 64 steps. Faster, but
  its correction is easy to get subtly wrong in hand-written assembly, and
  M0 checks correctness, not speed (ADR-2026-10-30-1230).
- **Restoring division for every divisor.** One path of 128 steps, but a
  zero divisor would give a value where every other width traps.
- **A convention of its own**, such as one routine that returns the
  quotient and the remainder in four registers. One routine fewer, but a
  convention that only this code knows, where System V is the one the
  backend's other calls follow.
- **Save the registers the routines use.** No value of the caller is in
  one.

## Consequences

- A division at `i128` costs a call and, for a divisor of `2^64` or
  more, 64 steps of a loop.
- A register allocator (M1) must treat a division at `i128` as a call
  that clobbers every caller-saved register.
- A function that divides at `i128` needs 24 bytes of stack below its
  frame at least, and its stack figure counts them.
- `crates/funk-x86-64/tests/div128.rs` pins the call and where the
  helper goes, `crates/funk/tests/i128_div.rs` runs each op natively
  against Rust's `i128` and `u128` arithmetic, and the corpus's
  `div-*-i128` modules check them against `fir-ref`.
