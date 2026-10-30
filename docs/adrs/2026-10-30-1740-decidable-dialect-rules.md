# The validation check asks a dialect for decidable equality on its types and for `DecidableDialectValidation`

Status: accepted

## Context

[#10](https://github.com/pmatos/funk/issues/10) asks for an executable
validation check that decides `Module.Valid`, written once for every
dialect (G0, ADR-2026-10-29-2016), "given decidable dialect rules". The
general rules of validation are decidable for any dialect once its types
can be compared: an op's operand, result and block argument types are
compared with those its op instance and its target block expect. A
dialect's own rules, `validTy` and `validOp` in `DialectValidation`, are
propositions, and the spec defines them as propositions so that each
dialect states its rules plainly.

## Decision

- The check, `Module.problems` (`lean/Fir/Validation/CheckModule.lean`),
  takes two things from a dialect, and nothing more:
  - `[DecidableEq d.Ty]`, the standard class;
  - an instance of the new class `DecidableDialectValidation d`
    (`lean/Fir/Validation/Check.lean`), whose two fields decide
    `validTy t` for every type and `validOp ctx o` for every context and op.
- `DialectValidation` is unchanged: its rules stay propositions. A dialect
  that wants the check proves its rules decidable, as the core dialect does
  case by case in `lean/Fir/Core/Check.lean`.
- The check is proved to agree with the rules in both directions:
  `Module.problems_eq_nil_iff : m.problems = [] ↔ m.Valid`. It gives the
  instance `Decidable m.Valid`.
- A dialect gives no reason when its own rule fails: the check says that
  the op breaks its dialect's own rule, and names the op.

## Alternatives

- **Boolean rules in `DialectValidation`.** It changes the spec's classes,
  and every dialect would write its rules twice, as a `Bool` and as the
  proposition that proofs use.
- **A reason in the class, such as `whyNot : OpContext d → d.Op → Option
  String`.** More readable messages, but another field with a law tying it
  to `validOp`; tools compare verdicts, never messages
  (ADR-2026-10-30-1032).
- **`DialectText` for messages that print types.** The check would depend on
  the text format, which the validation chapter does not need.

## Consequences

- A new dialect gets the check, and so `fir-ref validate`, by deriving
  `DecidableEq` for its types and deciding its two rules.
- Messages about a type or a dialect rule do not print the type or the op
  instance; they name the value, the op's index and its block.
