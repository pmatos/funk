# A word that names a core op is a core word in generic code, whatever else it means

Status: accepted
Tier: direction; area: semantics

## Context

G0's source checks (ADR-2026-11-03-0600) fail when generic code writes a
word of the core dialect's text alone as a string: `scripts/check_g0.py`
takes the words from the strings of `lean/Fir/Core/Text.lean`, and
`crates/funk-ir/tests/g0.rs` from the dialect's registration. They match
whole strings, so a message that holds a word, such as
`a poison divisor`, is not one.

ADR-2026-10-29-2006 adds the op `poison`. Its name is also S1's word for
the deferred-UB value, which the generic spec is about: `PoisonOr`,
`TyPoison`, `PoisonClass`. A check that reads words cannot tell which of
the two a string means. On `main` at #122, no generic file of either
language writes `"poison"` alone: generic Lean names the value with
Lean's names, and `fir-ref`'s command line, which spells it in its
reports, may name core ops (ADR-2026-11-03-0600).

## Decision

- **The rule.** A word that names a core op is a word of the core
  dialect, whatever else it means. Generic code does not write it alone
  as a string. It names the concept with the spec's own definitions,
  such as `PoisonOr.poison` and `TyPoison.IsPoison`, and leaves the
  spelling to code that may name core ops: the dialect's files and
  `fir-ref`'s command line, which spells a poison value `poison`.
- **A sentence is not a word.** A string that holds the word among other
  text, such as a message, stays allowed, as before.
- **No exemptions.** Neither check has a list of words that generic code
  may write. Both take `poison` from the dialect, as they take every
  op's name.
- **The checks pin it.** `scripts/test_check_g0.py` plants a generic
  Lean file that writes `"poison"` alone, which fails, and a message and
  an interpolated string that hold it, which pass; the same file under
  `lean/Fir/Core/` passes. `g0.rs` checks that `poison` is a word of the
  registration, and plants Rust code: `"poison"` alone is found, and a
  message, a comment or a unit test that holds it is not.

## Alternatives

- **Exempt the generic terms.** A list with `poison` on it would let
  per-op code for the op `poison` into generic code unseen.
- **Rename the op.** The human's ruling names it `poison`.

## Consequences

- Generic code that one day needs the bare spelling, such as a generic
  report of outcomes, takes it from the dialect through a class, or an
  ADR moves the line.
- A later op whose name is also a generic term falls under the same
  rule, with no change to either check.
