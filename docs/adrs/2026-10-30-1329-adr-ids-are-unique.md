# ADR ids are unique: a taken minute adds the seconds, and a hook checks it

Status: accepted

## Context

An ADR is named `YYYY-MM-DD-HHMM-slug.md` and cited as `ADR-YYYY-MM-DD-HHMM`
(`docs/adrs/README.md`). The README said two authors do not pick the same
minute independently. Parallel agents did: PR #34 merged
`2026-10-30-1031-publish-spec-to-github-pages.md`, and PR #35 then added
`2026-10-30-1031-generic-ops-and-registry.md`. CI passed on #35's merge ref,
because no check compared ids. Two ADRs with one id make every citation of
that id ambiguous. #35 renamed its ADR by hand.

## Decision

- An ADR keeps the name `YYYY-MM-DD-HHMM-slug.md`, with the UTC time it was
  written. When an ADR already holds that minute, the newer one adds the
  seconds: `YYYY-MM-DD-HHMMSS-slug.md`, cited as `ADR-YYYY-MM-DD-HHMMSS`.
  Existing ADRs keep their names.
- An ADR's id is its whole timestamp, so `ADR-2026-10-30-1031` and
  `ADR-2026-10-30-103112` are two ids.
- The `adr-ids` pre-commit hook (`scripts/check_adr_ids.py`) reads every file
  that git tracks under `docs/adrs/` except `README.md`. It fails when a name
  does not have one of the two forms, with ASCII digits, a real date and time
  and a slug of lower-case words joined by hyphens, and when two files share
  an id. On a clash it names every file with that id and says to give the
  newer one a second no other ADR uses. It cannot tell which ADR is newer or
  whether a minute was taken when an ADR was named, so it accepts either form
  on its own; review keeps the seconds form for a taken minute.
- The hook does not take pre-commit's file list: a commit that adds one ADR
  must still be checked against the ADRs already on `main`. It reads git's
  index, not the directory, so untracked files such as editor swap files do
  not fail a commit.
- `scripts/test_check_adr_ids.py` tests the hook; the `adr-ids-test` hook
  runs it when either file changes.

## Alternatives

- **Sequence numbers.** Concurrent PRs collide on "the next number" far more
  often than on a minute, and renumbering breaks citations.
- **Seconds on every new ADR.** No clash needs fixing then, but the names of
  existing and new ADRs would differ for no reason in the common case.
- **Rename to the next free minute.** The name would no longer give the time
  the ADR was written.

## Consequences

- CI runs `pre-commit run --all-files` on a PR's merge ref, so a PR whose ADR
  clashes with one on `main` fails there.
- The ruleset does not require a branch to be up to date before merging. Two
  PRs that pass CI apart can still merge a clash; the push to `main` then
  fails the hook, and so does every later PR until the newer ADR is renamed.
- A citation of a minute-form id is a prefix of a seconds-form id of the same
  minute, so a search for one must stop at the end of the digits.
