# A dialect's function rule sees the host function through a view

Status: accepted
Tier: direction; area: validation

## Context

ADR-2026-10-29-2016 says that the verifier will need a hook for use-once
(linear) values. A use-once rule is about every use of a value in a
function, so no rule of one op can state it.

A module's dialects combine as a sum routed by prefix, the sum moves into the
spec, and it covers types as well as ops (ADR-2026-11-09-1543).
ADR-2026-11-09-1545 leaves use-once values to the toy test of
[#167](https://github.com/pmatos/funk/issues/167).

A `Func (SumDialect Ty Op₁ Op₂)` is not a function of either side. A rule
typed `Func d → Prop` therefore cannot be lifted through the sum, and mapping
the function to one side would drop the other side's ops and their uses.

## Decision

- **The rule.** `DialectValidation` gains `validFunc`, and `Func.Valid` gains
  a field that requires it. In `funk-ir`, a dialect registers a `FuncSpec`
  with `Dialect::func_rule`, and `verify` runs every registered rule on every
  function. The core dialect has no such rule.
- **A view of the host.** `validFunc` is polymorphic in the dialect `host`
  that holds the dialect, and takes a `DialectView d host`, which maps a
  host op or type to `d`'s, or to `none` when it belongs to another dialect.
  The rule sees the whole function, and a sum gives each side its own view,
  so a dialect's rule is written once and works in any sum. The Rust rule
  needs no view, because ops and types are data there.
- **Its context.** The rule reads the module's symbol table, in a
  `FuncContext`. It does not take `ModuleContext`, because the check holds a
  `Lookup`, which cannot give back the location table's keys.
- **Every function.** Validation calls the rule also on a function that
  breaks other rules, so a rule assumes nothing about the function.
- **Location.** A function has no location of its own. A broken function rule
  is reported at the function's entry block, with the location reference of
  its first op, on both sides.
- **No reason in Lean.** As for op rules (ADR-2026-10-30-1740), the Lean rule
  is a decidable proposition, and the check gives a fixed message. The Rust
  rule returns its reason. Tools compare verdicts, never words
  (ADR-2026-10-30-1032).
- **The test.** A use-once toy dialect on each side reads the same
  `tests/dialects/use-once.cases`, so the two validators face the same
  must-accept and must-reject texts. The file is an input of the `FirTest`
  library in `lean/lakefile.lean`, because Lake does not rebuild a module
  when a file that it includes changes.

This refines ADR-2026-10-29-2016, and extends the class of
ADR-2026-10-30-1740 with a third rule to decide.

## Alternatives

- **`validFunc : ModuleContext d → Func d → Prop`, with each sum supplying
  its own rule.** It is simpler now. But a dialect's rule would not compose
  when the sum moves into the spec, and the hook would have to be reshaped
  after dialects depend on it. The Rust registry already composes the rules.
- **A located reason in the class.** It would point at the broken use, at
  the cost of another field and a law tying it to the rule, which
  ADR-2026-10-30-1740 rejected for op rules.

## Consequences

- A new dialect states a function rule once, and it holds in every sum.
- A rule that walks a function pays for its own walk. The core dialect pays
  nothing, and the walk of a rule must meet the no-nesting-limit rule
  (ADR-2026-10-30-1549) before a real dialect uses one in `fir-ref`.
- A use-once failure points at the entry block, not at the broken use.
- The ticket that moves the sum into the spec keeps this shape, with
  `DialectView.ty` carrying the projection of the summed types.
- `funk-ir` runs every registered rule today. When a module declares its
  dialect set (ADR-2026-11-09-1543), the verifier must run only the rules of
  the declared dialects, as the sum of that set does in Lean.
