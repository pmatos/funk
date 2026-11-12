# A dialect's validation rules are decidable propositions, and its function rule sees the host function through a view

Status: accepted
Tier: direction; area: validation

## Decision

- **The check asks two things of a dialect, and nothing more.** The spec's
  check, `Module.problems` (`lean/Fir/Validation/CheckModule.lean`), takes
  `[DecidableEq d.Ty]` and an instance of `DecidableDialectValidation d`
  (`lean/Fir/Validation/Check.lean`), whose fields decide each of the
  dialect's own rules. Those rules, in `DialectValidation`, stay
  propositions; a dialect proves them decidable, as the core does in
  `lean/Fir/Core/Check.lean`. `Module.problems_eq_nil_iff` proves that the
  check finds no problem exactly when the module is valid, which gives
  `Decidable m.Valid`.
- **A rule over a whole function.** `DialectValidation` has `validFunc`, and
  `Func.Valid` requires it; it states what no op rule can, such as a value
  used exactly once. It is polymorphic in the dialect `host` that holds the
  dialect, and takes a `DialectView d host`, which maps a host op or type to
  `d`'s, or to `none`. It reads the module's symbol table in a
  `FuncContext`. Validation calls it on every function, also one that breaks
  other rules. In `funk-ir` a dialect registers a `FuncSpec` with
  `Dialect::func_rule`, and `verify` runs every registered rule; ops and
  types are data there, so it needs no view. The core has no such rule.
  A rule pays for its own walk of the function, which must meet the
  no-nesting-limit rule (ADR-2026-10-30-1549) before a real dialect uses
  one in `fir-ref`. `funk-ir` must come to run only the rules of a module's
  declared dialects, as the sum of that set does in Lean.
- **No reason in Lean.** When a dialect's own rule fails, the check gives a
  fixed message with the op's index and block. It prints neither the type
  nor the op instance. The Rust rule returns its reason. Both sides report a
  broken function rule at the function's entry block, with its first op's
  location.
- **Shared cases.** `tests/dialects/use-once.cases` is read by a use-once
  toy dialect on each side, and is an input of the `FirTest` library in
  `lean/lakefile.lean`, since Lake does not rebuild a module when a file it
  includes changes.

This refines the use-once hook of ADR-2026-10-29-2016.

## Why

A dialect states its rules plainly, once, and gets the check, and so
`fir-ref validate`. A function rule written over a view holds in any sum of
dialects (ADR-2026-11-09-2306), where a `Func` of the sum is a function of
neither side. Tools compare verdicts, never words (ADR-2026-10-30-1032).

## Rejected alternatives

- **Boolean rules in `DialectValidation`.** Every dialect would write each
  rule twice, as a `Bool` and as the proposition that proofs use.
- **A reason in the class, such as `whyNot`, or a located reason.** Another
  field, with a law tying it to the rule.
- **`DialectText` for messages.** A third instance and its printer for every
  dialect that wants the check.
- **`validFunc : ModuleContext d → Func d → Prop`, supplied per sum.** It
  would not compose when the sum moved into the spec. `ModuleContext` is
  also out because the check holds a `Lookup`, which cannot give back the
  location table's keys.
