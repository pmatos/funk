# A ported LLVM function whose name the spelling check rejects keeps its name, spelled correctly

Status: accepted
Tier: implementation; area: testing-and-harness

## Context

ADR-2026-11-03-0644 keeps LLVM's names of functions in the cases ported
to fir, and leaves out a function whose name the repository's spelling
check, the `typos` hook, rejects, as an exception to that check is a
human call. That rule left out three functions of
`llvm/test/Transforms/InstSimplify/rem.ll`, lines 516 to 545: a fold of
a `urem` of a `mul nuw` by a multiple of the divisor, and its two
negative tests. LLVM's names for them misspell "simplify": they drop its
second "i". The human ruled on 2026-11-03, by dialog, that they are
ported under the correct spelling, and that the spelling check gets no
exception ([#124](https://github.com/pmatos/funk/issues/124)).

## Decision

This refines ADR-2026-11-03-0644's rule on names that the spelling check
rejects. Its other rules stand.

- A function that ADR-2026-11-03-0644 would port but for its name is
  ported under LLVM's name with the misspelled word spelled correctly.
  Nothing else in the name changes.
- The misspelled word is written nowhere in the repository. Each test of
  such a function has a `from` that names the function by its file and
  lines and says that LLVM's name misspells the word, and the sidecar's
  comment says the same.
- Its ops carry a location that is the function's lines, as every ported
  function's do (ADR-2026-11-03-0643), so the text still points at
  LLVM's definition.
- The spelling check, its configuration and its exclusions do not change.

## Alternatives

- **An exception to the spelling check for LLVM's word.** It keeps
  LLVM's names whole, but changes a check's exclusions; the human ruled
  against it.
- **Leaving such functions out**, as before. It loses folds and negative
  tests that M0's ops express, for a reason that has nothing to do with
  what they test.

## Consequences

- `tests/fir/llvm/instsimplify-rem.fir` holds `@simplify_urem_of_mul`,
  `@simplify_urem_of_mul_fail_bad_flag` and
  `@simplify_urem_of_mul_fail_bad_mod`.
- A ported name can differ from LLVM's. A reader finds the LLVM function
  by the file and lines that `from` and the location give, not by
  searching for the name.
- A later port that meets another rejected name follows this ADR, with
  no new ruling.
