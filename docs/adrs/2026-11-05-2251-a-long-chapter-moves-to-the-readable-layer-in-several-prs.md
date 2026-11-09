# A long chapter moves to the readable layer in several PRs of consecutive sections

Status: accepted
Tier: implementation; area: spec-site

## Context

ADR-2026-11-05-2012 moves the spec to the readable layer one chapter per
PR, after its pilot. The Execution chapter has about 55 sections and the
Text format chapter about 40. Each section needs a readable block for every
declaration of its Lean module, and its module prose rewritten in the same
voice ([#176](https://github.com/pmatos/funk/issues/176)). A whole chapter
of that size is too much for one review to read with care, and the review
is what keeps the prose true to the Lean.

## Decision

- A chapter moves to the readable layer in one PR or, when it is long, in
  several PRs, each of a run of consecutive sections of the chapter.
- Sections that have not moved yet keep rendering with `{includeLiterate}`,
  as before, so the spec is whole between the PRs.

## Consequences

- Each PR stays small enough to review against the Lean, line by line.
- Several batches can be written at once. They all edit `FirSpec.lean`, so a
  batch that lands later merges `main` and keeps both sides.
- For a while a chapter mixes readable sections and literate ones.
