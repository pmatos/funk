# A Python hook checks ADR citations in every tracked file, against the spec checker's cases

Status: accepted

## Context

The spec build fails on a citation of an ADR that does not exist
(ADR-2026-10-30-1439), but it reads only the spec's sources: the Lean files
of `lean/`, the files at the top of `docs/spec/` and the ADRs. A citation in
`AGENTS.md`, the roadmap, a workflow, the hook config or Rust and Python code
was not checked, so renaming an ADR under its citations (ADR-2026-10-30-1329)
left them pointing at nothing
([#44](https://github.com/pmatos/funk/issues/44)).

ADR-2026-10-30-1439 rejected a Python checker because two definitions of a
citation could disagree. On 2026-11-05 the human decided #44: a fast Python
pre-commit hook checks every citation in every tracked text file, with the
Lean checker's grammar, an explicit list of fixtures, its own test hook, and
test cases that both checkers share, so the definitions cannot drift.

## Decision

- **The hook.** `adr-citations` runs `scripts/check_adr_citations.py`. It
  reads every file that git tracks and that is text (UTF-8, no NUL byte, not
  a symbolic link). For each citation outside code whose id no tracked ADR
  has, it prints the spec checker's message,
  `FILE:LINE:COL: ADR-<id> names no ADR in docs/adrs/`, and its message for a
  malformed citation too. It runs on every commit (`always_run`), since
  deleting or renaming an ADR breaks citations in files the commit does not
  touch, and in CI with `--all-files`.
- **The grammar is the spec checker's.** The script ports
  `docs/spec/FirSpecSite/Citation.lean` line for line: `ADR-`, a date
  `YYYY-MM-DD-` and a run of digits, ASCII only. A citation ends at the run's
  last digit, so it matches a whole id; four or six digits are an id, any
  other number is malformed. A placeholder is not a citation. Code spans and
  fenced code blocks are blanked first: code is quoted, not cited. Lines end
  at a line feed, and columns count characters.
- **Real dates and times.** The grammar does not read the date. A citation
  names an ADR only when a tracked ADR's file name starts with its id, and
  `adr-ids` accepts only names with a real date and UTC time. So a citation
  of an impossible date or time names no ADR, in both checkers.
- **One table of cases.** `docs/spec/FirSpecSite/citation-cases.json` holds
  texts, the citations of each outside code with their line and column, and
  the messages that checking it as `a.md` gives, for a fixed list of known
  ids. The spec's tests read it with `include_str` and fail the build on a
  case they disagree with, and Lake rebuilds them when it changes, through an
  `input_file` that `FirSpecSite` needs. The hook's tests read the same file.
  A change to either grammar needs a case there, which both must pass.
- **Fixtures.** `FIXTURES` in the script lists, with a reason each, the files
  whose bad citations are test data on purpose. They are not checked. A
  listed file that git does not track, or that cites no missing ADR, fails
  the hook, so the list cannot go stale.
- **Tests.** `adr-citations-test` runs `scripts/test_check_adr_citations.py`
  when the script, its tests, the table or `scripts/check_adr_ids.py`
  changes. Both hooks have a step in the static job of `ci.yml`.

## Alternatives

- **The Lean checker for every file.** A commit would wait for Lean and
  Verso to build, which takes minutes in a fresh clone; the human asked for a
  fast hook.
- **Two test suites of their own.** Nothing would notice when the grammars
  part, which is the risk ADR-2026-10-30-1439 named.

## Consequences

- A broken citation anywhere in the repository fails the commit that breaks
  it, in well under a second, with its place.
- Two implementations of one grammar remain. The table keeps them in step on
  the cases it holds, so a change to either adds a case.
- A new file of test data with bad citations goes on the list, with its
  reason.
- ADR-2026-10-30-1439's last consequence, that citations outside the spec's
  sources are not checked, no longer holds.
