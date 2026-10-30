# Register allocation is spill-everything: every value has its own stack slot

Status: accepted

## Context

The roadmap makes spilling every value the baseline register allocation of
the M0 backend; M1 replaces it with real allocation. The baseline must be
simple enough to be right by reading it, since every later op family
builds on it. A frame holds a slot per value, so it can be far larger than
the guard region that Linux keeps below a stack: one page below a thread's
stack, and a gap of 1 MiB below the main stack by default.

## Decision

- **A slot per value.** Every value a function defines has an 8-byte slot
  of its own below `%rbp`: the parameters first, then each block's
  arguments and each op's results, in order. The `n`-th value, from 1, is at
  `-8n(%rbp)`.
- **The frame.** The prologue is `pushq %rbp; movq %rsp, %rbp`, then makes
  room for `S` bytes, where `S` is `8n` rounded up to 16, so `%rsp` is
  16-byte aligned wherever the function calls. The epilogue is
  `leave; ret`. A frame must fit 2 GiB, the reach of a 32-bit
  displacement; a function with more values is reported as unsupported.
- **Stack probes.** A frame of at most a page (4096 bytes) is one
  `subq $S, %rsp`. A larger one is probed: the prologue moves `%rsp` down a
  page at a time and touches each page with `orq $0, (%rsp)`, counting the
  pages in `%r11`, which carries no argument; then it subtracts the rest,
  less than a page. So every access to the stack is at most a page below
  one already made: the stack grows a page at a time, and a frame too
  large for its stack faults at the stack's end instead of jumping past the
  guard region into other memory.
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
- **No probes.** M0 writes its slots in order, downwards, so its stack
  already grows a page at a time. Branches (#19) and calls (#20) break
  that order: a call below an untouched frame can land past a guard page,
  in memory that another thread or mapping owns, with no fault.
- **A probe routine, as `__chkstk` on Windows.** The same probes, but a call
  in every large prologue, and a symbol that C code linking the object
  file would have to provide.

## Consequences

- Lowering an op is local: it needs only its operands' and results' slots.
- The code is slow and large: every op reads and writes memory.
- A frame larger than a page costs a loop in the prologue that touches
  each of its pages once.
- The stack a function runs on bounds its frame. The executable that
  `funk build` writes runs each function on a stack that it reserves for
  it (ADR-2026-10-30-1233), so there the 2 GiB limit is the bound, not the
  process's stack limit. A funk function that C code calls runs on its
  caller's stack, and a frame larger than what is left there ends with
  `SIGSEGV`, as a C function's would.
