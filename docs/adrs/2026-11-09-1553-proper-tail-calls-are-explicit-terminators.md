# A proper tail call is an explicit terminator that validation checks, and a chain of them runs in bounded space

Status: accepted
Tier: direction; area: semantics

## Decision

- **An explicit terminator.** `tail_call @f args`, and its indirect form
  (ADR-2026-11-09-1548), ends a block, calls the callee and returns the
  callee's results as the caller's own. Only marked calls are proper; a
  `call` followed by `ret` is promised nothing.
- **Validation.** The verifier rejects a tail call unless the callee's result
  types equal the caller's, no stack allocation of the caller is passed to the
  callee or reachable from its arguments, and the target's calling convention
  lets the callee reuse the caller's frame. Under System V on x86-64, the
  callee's stack arguments must fit in the caller's incoming stack-argument
  area.
- **The space promise.** The spec gives each run a frame depth, the number of
  calls that have not returned. A tail call replaces the caller's frame
  instead of adding one, so a chain of tail calls keeps the depth of its first
  caller. `fir-ref` and every backend keep this promise, and a native run
  checks it with deep tail recursion in the corpus.
- **Effects** are those of a call, plus control (ADR-2026-11-09-1541).

If the conditions or the promise meet a blocker in implementation, this ADR
and its page are edited in place.
[semantics-m1-design.md](../decisions/semantics-m1-design.md) states each
rule. The human placed proper tail calls (#100) in M1 as an explicit marker on
2026-11-09, on #204, accepted this design the same day, and confirmed on
2026-11-11, on #100, that it stands.

## Why

A frontend that guarantees tail calls, such as Vow, needs a call in tail
position to reuse the caller's frame, so tail recursion runs in constant
stack. fir already has loops, so only such frontends need it. The spec had no
measure of space: fuel counts steps, and fir has no depth limit.

## Rejected alternatives

- **Every call in tail position is proper,** as in Scheme. Some such calls
  cannot reuse the frame under System V, so the promise would sometimes fail
  silently, or force an expensive convention on every call.
