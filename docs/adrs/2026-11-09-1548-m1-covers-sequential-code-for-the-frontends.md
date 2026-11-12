# M1 gives the frontends what sequential code needs, and leaves hooks for concurrency, exceptions and contracts

Status: accepted
Tier: direction; area: process

## Decision

**M1's goal:** fir becomes an IR that the frontends can lower their
sequential code to, with concurrency, exceptions and contracts arriving
through hooks M1 leaves in the format.

**In M1:**

- **Indirect calls and function addresses.** An op gives a pointer to a
  function from its symbol (H3, ADR-2026-10-29-2012). A call through a pointer
  states the callee's signature. Calling through a pointer whose target has
  another signature is UB.
- **Calling variadic external functions** (ADR-2026-11-09-1547).
- **Stack allocation.** An op allocates in a memory for the current call, and
  the allocation is freed when the call returns. Heap allocation stays a call
  to an external function such as `malloc`, with no op of its own.
- **Volatile accesses.** A `volatile` attribute on loads and stores makes the
  access an event of the trace (ADR-2026-11-09-1540). It cannot be removed,
  duplicated or reordered with other events.
- **`unreachable`.** A terminator that is immediate UB when reached.
- **Proper tail calls** (ADR-2026-11-09-1553), and **memory intrinsics** and
  **inline assembly** (ADR-2026-11-09-1551, ADR-2026-11-09-1552).

**Out of M1, with a hook in the format:**

- **Defining variadic functions** (`va_start`, `va_arg`). The signature syntax
  admits them, and the verifier rejects a definition until the C frontend (M4)
  needs one.
- **Concurrency (S6).** The `ordering` attribute on memory ops
  (ADR-2026-11-09-1542).
- **Exceptions and unwinding.** A dialect may add terminators with extra
  successors, such as a call with an unwind successor, so no format change is
  needed.

**Out of M1:** contract ops. They come as Vow's own dialect in M3.

Each item in M1 goes through every layer, and the roadmap's M1 section and #177
list them. The human ruled this split on 2026-11-09, in #201.

## Why

M1's goal (ADR-2026-11-05-2255) said fir becomes an IR that real programs and
the Vow, C and C++ and Linux frontends can lower to. Its scope left out
features those frontends need, and named neither inclusion nor exclusion for
several of them. C code that defines variadic functions, uses atomics or
throws cannot be lowered until M4 or later.

## Rejected alternatives

- **Keep the old goal sentence.** M1's scope did not deliver it, so the goal
  and the scope disagreed.
- **Leave these features unnamed.** Each would have had no place in any
  milestone until an agent chose one, which is a direction call.
