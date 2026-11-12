# A Python hook checks ADR citations in every tracked file, against the spec checker's cases

Status: accepted
Tier: direction; area: process

## Decision

- The `adr-citations` hook runs `scripts/check_adr_citations.py` on every
  commit, and in CI with `--all-files`. It reads every tracked text file
  (UTF-8, no NUL byte, not a symbolic link). It fails on a malformed citation,
  on a citation outside code of an ADR that no tracked ADR has, and on a
  citation of a removed ADR, naming where its rule lives now.
- The grammar is the spec checker's: the script ports
  `docs/spec/FirSpecSite/Citation.lean` line for line. A citation ends at its
  last digit, so it matches a whole id; four or six digits after the date are
  an id, and any other number is malformed. A placeholder is not a citation.
  Code spans and fenced code blocks are blanked first, because code is quoted,
  not cited.
- One table of cases, `docs/spec/FirSpecSite/citation-cases.json`, is read by
  the spec's tests and by the hook's tests. A change to either grammar adds a
  case there, which both must pass.
- `FIXTURES` in the script lists, each with a reason, the files whose bad
  citations are test data on purpose. A listed file that git does not track,
  or that cites no missing ADR, fails the hook.

The human decided this on 2026-11-05, in #44.

## Why

The spec build checks citations only in the spec's own sources. A citation in
`AGENTS.md`, the roadmap, a workflow, the hook config or Rust and Python code
was not checked, so renaming or deleting an ADR left them pointing at nothing.
The spec's appendix had rejected a second checker because two definitions of a
citation could disagree; the shared table of cases keeps them in step.

## Rejected alternatives

- **The Lean checker for every file.** A commit would wait for Lean and Verso
  to build, which takes minutes in a fresh clone; the human asked for a fast
  hook.
- **Two test suites of their own.** Nothing would notice when the grammars
  part.
