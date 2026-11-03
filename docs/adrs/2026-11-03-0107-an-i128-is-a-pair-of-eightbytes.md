# An i128 is a pair of eightbytes in two slots, and each op lowers it through a register pair

Status: accepted

## Context

S2 puts `i128` in the M0 backend through register pairs, with division
through a runtime helper (ADR-2026-10-29-2007);
[#21](https://github.com/pmatos/funk/issues/21) does every op but
division, and [#22](https://github.com/pmatos/funk/issues/22) does
division. Every value has an 8-byte slot below `%rbp`
(ADR-2026-10-30-1230), and a value of `iN`, `N` at most 64, is the low
`N` bits of its slot, with the bits above unspecified
(ADR-2026-10-30-1231). Native code holds no poison, and `freeze` is a
copy (ADR-2026-10-30-2248). x86-64 has no 128-bit integer registers, but
it carries between 64-bit ones: `adc` and `sbb` add and subtract a carry,
`mul` gives a 128-bit product in `%rdx:%rax`, and `shld` and `shrd` shift
bits from one register into another.

## Decision

- **Two slots.** An `i128` value takes two slots next to each other in
  its frame, its low half at the lower address: the value that ends with
  the `n`-th slot has its low half at `-8n(%rbp)` and its high half at
  `-8n + 8`. So its 16 bytes are the value in little-endian order, as an
  `__int128` is in memory. Each half is 64 bits of the value; no bit is
  unspecified. `width::check` accepts `i128`, and `width::words` gives it
  two eightbytes.
- **A register pair.** An op at `i128` loads each operand's low half into
  `%rax` and its high half into `%rdx`, computes, and stores both halves.
  - `const` writes two immediates. `add` is `addq` and `adcq`, `sub`
    `subq` and `sbbq`. `mul` is `mulq` of the low halves, and the low 64
    bits of the two cross products, each by `imulq` in `%rcx`, added into
    `%rdx`. Their flags lower as no flags do (ADR-2026-10-30-2248).
  - `and`, `or` and `xor` apply to each half.
  - A shift reads the low half of its amount into `%rcx`. `shldq` or
    `shrdq` by `%cl` moves bits between the halves, and `shlq`, `shrq` or
    `sarq` shifts the half they fill; x86 masks those counts to 6 bits.
    `testb $64, %cl` and two `cmovneq` then move the halves one place
    further for an amount from 64 to 127, filling with zero, or with the
    sign for `ashr`, from `%rsi`. No code branches on the amount. An
    amount of 128 or more gives poison, and gets whatever this sequence
    gives for its low 7 bits.
  - `icmp eq` and `ne` `xorq` each half with the other operand's and
    `orq` the two. Every other predicate is `cmpq` of the low halves and
    `sbbq` of the high ones, then `setl`, `setge`, `setb` or `setae`, with
    the operands swapped for `sgt`, `sle`, `ugt` and `ule`: that borrow
    chain sets the carry, sign and overflow of the 128-bit subtraction,
    but not its zero flag.
  - `select` tests bit 0 of its condition and moves in each half of its
    second value with a `cmovzq` of its own.
  - `zext` and `sext` to `i128` extend the operand to 64 bits with
    `width::extend`; the high half is zero, or `sarq $63` of the low one.
    `trunc` from `i128` copies the low half.
  - A branch passes an `i128` to a block argument as two copies of its
    parallel move, one per half (ADR-2026-10-31-0335): a swap of two
    `i128`s is two cycles.
  - `ret` returns an `i128` in `%rdx:%rax`; ADR-2026-11-03-0108 says how
    calls pass and return it.
- **Division waits.** `sdiv`, `udiv`, `srem` and `urem` at `i128` are
  reported at the op, with its result's name, until #22's helper.
- **Poison is not tracked per half.** Native code holds no poison
  (ADR-2026-10-30-2248): where the source gives poison, the two slots
  hold some bits. `freeze` copies both halves into its own two slots,
  which no other op writes, and every use reads those, so every use of a
  frozen value sees the same 128 bits, both halves of one value.

This refines ADR-2026-10-30-1230, whose values each had one slot, and
ADR-2026-10-30-1231, which reported `i128` until #21.

## Alternatives

- **The high half at the lower address.** Pushing a stack argument and
  reading an `__int128` that C passes would then swap the halves.
- **SSE registers.** They hold 128 bits, but have no 128-bit add,
  multiply, shift or compare, and no carry.
- **A branch on bit 6 of the shift amount**, to code for below 64 and for
  64 or more. Two labels and a jump in every shift; the `cmov` form has
  none.
- **A poison bit per value**, or per half. Native code cannot hold
  poison without tracking it, and nothing reads it: any value refines
  poison.

## Consequences

- An op at `i128` is a few instructions on two registers. It clobbers
  `%rax`, `%rcx` and `%rdx`, and a shift `%rsi` too, which is free while
  every value lives in its slots; a register allocator (M1) needs pairs
  and must treat those as clobbered.
- An `i128` takes 16 bytes of its frame, so frames, and the stack figure
  that sums them (ADR-2026-11-02-1132), grow with them.
- `crates/funk-x86-64/tests/pair.rs` pins each sequence;
  `crates/funk/tests/i128_ops.rs` runs each op natively against Rust's
  `i128` and `u128` arithmetic; the corpus's `*-i128` modules check them
  against `fir-ref`.
- A later optimizer (M1) that makes poison real must keep the two halves
  of a frozen value one value, as for any width.
