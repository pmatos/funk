# An i128 argument takes two registers or sixteen aligned bytes of the stack, and an i128 result comes back in RDX:RAX

Status: accepted

## Context

A funk function is a System V AMD64 function (ADR-2026-10-30-1232): its
integer arguments go in `%rdi`, `%rsi`, `%rdx`, `%rcx`, `%r8` and `%r9`,
then on the stack, and its result in `%rax`. C code may call it. That ADR
gives each argument 8 bytes, and [#21](https://github.com/pmatos/funk/issues/21)
adds `i128`, two eightbytes (ADR-2026-11-03-010730).

System V passes an `__int128` as two eightbytes of class INTEGER. Both go
in registers when two are free, and otherwise the whole argument goes on
the stack, aligned to 16 bytes; a register left free goes to a later
argument. It returns an `__int128` with its low half in `%rax` and its
high half in `%rdx`. gcc 16 and clang lay out these four C prototypes
alike, with `long` for one eightbyte:

- `g1(long a, b, c, d, e, __int128 x, long y)`: `x` at 0 and 8 above
  `%rsp` at the call, and `y` in `%r9`.
- `g2(long a, b, c, d, e, f, s, __int128 x, long t)`: `s` at 0, a hole,
  `x` at 16, `t` at 32, and 48 bytes in all.
- `g3(__int128 a, b, c, d, long e)`: `a`, `b` and `c` in register pairs,
  `d` at 0, `e` at 16.
- `g4(long a, __int128 b, c, d)`: `d` at 0, and `%r9` unused.

Four places read where arguments go: the caller (`abi::call`, which
ADR-2026-11-02-1428 makes the one emitter of outgoing calls), the
callee's prologue, the entry wrapper, which calls through `abi::call`,
and the entry's stack figure (ADR-2026-11-02-1132).

## Decision

- **One layout.** `abi::layout`
  ([`crates/funk-x86-64/src/abi/layout.rs`](../../crates/funk-x86-64/src/abi/layout.rs))
  maps the arguments of a call, each of one or two eightbytes, to their
  places by System V's rules above, and pads the stack area to a multiple
  of 16. The caller, the prologue and the stack figure all read it, so
  they cannot disagree. Its tests pin the four layouts above.
- **The caller** pushes the stack area from the top down, one `pushq` per
  eightbyte, the high half of an `i128` before its low half, and a hole
  as `subq $8, %rsp`; then it loads the registers. A call with no `i128`
  is the same as before. It extends no argument
  (ADR-2026-11-02-1021).
- **The callee** stores each eightbyte of its parameters from its
  register, or from `16 + offset(%rbp)` for one at `offset` above `%rsp`
  at the call.
- **The result.** `ret` of an `i128` puts its low half in `%rax` and its
  high half in `%rdx`, and a call stores both into its result's slots.
- **The stack figure** counts the words that a call pushes from the same
  layout, by the eightbytes of the call's operands.
- **The executable.** The wrapper parses an `i128` argument into two
  slots and passes `%rdx`, the high half of an `i128` result, to the
  printer. The runtime's routines that parse arguments and print results
  work on 128 bits at every width.

This refines ADR-2026-10-30-1232: an `i128` takes two eightbytes, in a
register pair or on the stack, and returns in `%rdx:%rax`. It refines
ADR-2026-10-30-1233 for the executable's wrapper and runtime, and
ADR-2026-11-02-1132 for the stack figure, which now reads the layout
that `abi::call` reads.

## Alternatives

- **Split an `i128` between `%r9` and the stack.** That is not System V:
  a C caller puts it all on the stack, and passes the next argument in
  `%r9`.
- **No alignment on the stack.** Also not System V, for the same reason.
- **Pass an `i128` by reference** to a copy. It would cost a copy per
  call, and C could not call such a function as one that takes an
  `__int128`.

## Consequences

- C code can call a funk function with `__int128` arguments and result,
  in any of the layouts above; a C program linked with the object file
  was checked by hand with gcc 16 and clang on the four prototypes.
- A call with `i128` arguments may leave a register unused and a hole on
  the stack.
- The runtime's value routines grew past what `runtime.s` can hold
  within its budget (ADR-2026-10-28-0724), so they move to
  `entry/values.s`, which follows it in the entry file.
- Where an `i128` goes when a function returns several values is #31's
  to decide; whichever of #21 and #31 lands second tests an `i128` among
  several results.
