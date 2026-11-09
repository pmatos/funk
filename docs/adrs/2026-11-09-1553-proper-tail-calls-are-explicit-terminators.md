# A proper tail call is an explicit terminator that validation checks, and a chain of them runs in bounded space

Status: proposed

## Context

[#100](https://github.com/pmatos/funk/issues/100) asks for proper tail
calls: a call in tail position reuses the caller's frame, so tail recursion
runs in constant stack. fir already has loops, so only a frontend that
guarantees tail calls needs them. The spec has no notion of stack space:
fuel counts steps, and fir has no depth limit. The human placed #100 in M1,
as an explicit marker, on 2026-11-09
([#204](https://github.com/pmatos/funk/issues/204)). This ADR proposes the
design that #100 asks the human to accept.

## Decision

- **An explicit terminator.** `tail_call @f args` (and its indirect form,
  ADR-2026-11-09-1548) ends a block, calls the callee, and returns the
  callee's results as the caller's own. Only marked calls are proper; a
  `call` followed by `ret` is not promised anything.
- **Validation.** The verifier rejects a tail call unless:
  - the callee's result types equal the caller's;
  - no stack allocation of the caller is passed to the callee or reachable
    from its arguments;
  - the target's calling convention lets the callee reuse the caller's
    frame. Under System V on x86-64, that means the callee's arguments
    passed on the stack fit in the caller's incoming stack-argument area.
- **The space promise.** The spec gives each run a frame depth: the number
  of calls that have not returned, where a tail call replaces the caller's
  frame instead of adding one. A chain of tail calls keeps the depth of its
  first caller. `fir-ref` and every backend keep this promise, and a native
  run checks it with deep tail recursion in the corpus.
- **Effects** are those of a call, plus control (ADR-2026-11-09-1541).

## Alternatives

- **Every call in tail position is proper,** as in Scheme. Some such calls
  cannot reuse the frame under System V, so the promise would sometimes
  fail silently, or force an expensive convention on every call.

## Consequences

- Vow, or any frontend that guarantees tail calls, can rely on them.
- The spec gains a measure of space for the first time.
- The status becomes accepted when the human accepts the conditions above.
