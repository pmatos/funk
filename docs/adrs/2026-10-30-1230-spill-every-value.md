# Register allocation is spill-everything: every value has its own stack slot

Status: accepted

## Context

The roadmap makes spilling every value the baseline register allocation of
the M0 backend; M1 replaces it with real allocation. The baseline must be
simple enough to be right by reading it, since every later op family
builds on it.

## Decision

- **A slot per value.** Every value a function defines has an 8-byte slot
  of its own below `%rbp`: the parameters first, then each block's
  arguments and each op's results, in order. The `n`-th value, from 1, is at
  `-8n(%rbp)`.
- **The frame.** The prologue is `pushq %rbp; movq %rsp, %rbp; subq $S,
  %rsp`, where `S` is `8n` rounded up to 16, so `%rsp` is 16-byte aligned
  wherever the function calls. The epilogue is `leave; ret`. A frame must
  fit 2 GiB, the reach of a 32-bit displacement; a function with more
  values is reported as unsupported.
- **Parameters.** The prologue stores each parameter in its slot: the
  first six from their registers, the rest from the caller's stack
  (ADR-2026-10-30-1232).
- **Ops.** An op loads its operands from their slots into scratch
  registers, computes, and stores its results into their slots. No value
  stays in a register from one op to the next. The scratch registers are
  caller-saved ones (`%rax`, `%rcx`, `%rdx` and the argument registers),
  so a function saves only `%rbp`.

## Alternatives

- **A simple linear-scan allocator now.** Faster code, but M0 checks
  correctness, not speed, and M1 brings real allocation.

## Consequences

- Lowering an op is local: it needs only its operands' and results' slots.
- The code is slow and large: every op reads and writes memory.
- Slots are written in order, downwards, so the stack grows a page at a
  time without probes. A frame larger than the stack limit, 8 MiB by
  default (about a million values), crashes when it runs.
