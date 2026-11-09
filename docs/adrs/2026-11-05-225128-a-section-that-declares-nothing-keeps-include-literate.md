# A section whose module declares nothing keeps includeLiterate

Status: accepted
Tier: implementation; area: spec-site

## Context

ADR-2026-11-05-2012 moves each section of the spec to the readable layer:
`{includeReadable}` shows a readable block in place of each declaration of
the section's Lean module, and fails unless the section's document explains
every declaration and has at least one readable block. That last check
catches a document that was never imported. Some modules hold only prose:
`Fir.Execution.PoisonUB`, which explains poison and immediate UB in plain
words, declares nothing.

## Decision

- A section whose Lean module declares nothing keeps `{includeLiterate}`.
  With no declaration, there is no Lean to hide and no readable block to
  write, and `{includeLiterate}` renders its module prose alone, as
  `{includeReadable}` would.
- Its module prose is still rewritten in the readable voice, in the PR
  that moves the sections around it.
- `{includeReadable}` keeps its check that a document has a readable block.

## Consequences

- Such a section looks like the readable sections around it, with no
  document in `docs/spec/FirSpec/` of its own.
- If the module gains a declaration, its section moves to
  `{includeReadable}` with a document, as any other.
