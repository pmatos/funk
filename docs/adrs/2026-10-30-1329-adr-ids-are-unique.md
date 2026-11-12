# ADR ids are unique: a taken minute adds the seconds, and a hook checks it

Status: accepted
Tier: direction; area: process

## Decision

- An ADR is named `YYYY-MM-DD-HHMM-slug.md`, with the UTC time it was
  written. When an ADR already holds that minute, the newer one adds the
  seconds: `YYYY-MM-DD-HHMMSS-slug.md`, cited as `ADR-YYYY-MM-DD-HHMMSS`.
- An ADR's id is its whole timestamp, so the minute form and the seconds form
  of one minute are two ids.
- The `adr-ids` hook (`scripts/check_adr_ids.py`) reads every file that git
  tracks under `docs/adrs/`, not pre-commit's file list, so a new ADR is
  checked against those already on `main`. It fails on a name without one of
  the two forms (ASCII digits, a real date and time, a slug of lower-case
  words joined by hyphens), on two files with one id, and on an id that a row
  of `docs/adrs/removed.json` holds. It cannot tell which ADR is newer, so it
  accepts either form; review keeps the seconds form for a taken minute.
- CI runs the hook in the `static` job, on each pull request's merge with
  `main`. A pull request merges only when it is up to date with `main`
  (ADR-2026-10-28-0725), so the second of two clashing pull requests falls
  behind, updates, and fails `adr-ids` before it merges.
- A minute-form id is a prefix of a seconds-form id of the same minute, so a
  search for a citation stops at the end of the digits.

The human ruled the naming rule on 2026-10-30, in #38.

## Why

Two ADRs with one id make every citation of it ambiguous. Parallel agents did
pick one minute: #34 and #35 both named an ADR for 2026-10-30 10:31, and CI
passed on #35's merge because no check compared ids. #35 renamed its ADR by
hand.

## Rejected alternatives

- **Sequence numbers.** Concurrent PRs collide on "the next number" far more
  often than on a minute, and renumbering breaks citations.
- **Seconds on every new ADR.** No clash would need fixing, but the names of
  existing and new ADRs would differ for no reason in the common case.
- **Rename to the next free minute.** The name would no longer give the time
  the ADR was written.
