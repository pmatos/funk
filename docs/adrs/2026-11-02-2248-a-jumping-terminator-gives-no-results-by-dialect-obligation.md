# In M0, a terminator that jumps gives no results by its dialect's obligation

Status: accepted
Tier: direction; area: semantics

## Decision

- No spec definition changes. Validation has no rule that a terminator has
  no results, and `Exit` carries no values, so a run never binds a
  terminator's results.
- "A terminator that jumps gives no results" is a condition that each
  dialect meets for its own terminators: if `exit` may give `goto i`, then
  `i` names a successor the op has and the op has no results. It is half of
  the `jumps` field of `Func.Local` and `Func.InModule`.
- The generic progress and no-stuck theorems cover a function only through
  those hypotheses. So "a validated module never gets stuck" holds only for
  a dialect whose terminators meet the condition. A dialect author who adds a
  terminator proves it, to have the theorems.
- The core dialect meets it (`Core.Op.exit_goto`), so no path of a run of a
  function of a valid core module is stuck (`Core.neverStuck`).
- `Exit` does not grow in M0. M4's design of exceptions and unwinding, the
  first place where a terminator with results makes sense, chooses between a
  validation rule and values on `Exit`, and edits this ADR in place.

The human ruled this on 2026-11-02 (#89, option c).
[semantics-interpreter.md](../decisions/semantics-interpreter.md#stuck-paths)
states what holds.

## Why

In a dialect with a terminator that jumps and has results, a valid function
that uses one of them in a block the terminator's block dominates gets
stuck. The core is not affected: `br` and `cond_br` have no results, and
`ret` never jumps. Either fix constrains how unwinding is modelled, so it
waits for that design, and no fir program's meaning or proof changes now.

## Rejected alternatives

- **A generic validation rule:** a terminator has no results. It closes the
  gap for every dialect, but forbids an `invoke`-style terminator, whose
  result is defined on one of its successors.
- **`Exit` carries values:** the run binds them on the jump. It changes
  `DialectDenote.exit`, the run and likely the scope rule, since such a
  result may be defined on only some edges, and its shape depends on how
  unwinding is modelled.
