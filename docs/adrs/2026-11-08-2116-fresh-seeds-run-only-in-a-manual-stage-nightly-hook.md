# Fresh seeds run only in a nightly workflow, through a manual-stage hook

Status: accepted

## Context

A fresh seed on each pull request would break "a local pass predicts a CI
pass" (ADR-2026-11-05-1408), and a failure could land on an unrelated pull
request. The human ruled on 2026-11-08, in #165, that pull requests run fixed
seeds and that only a nightly job draws fresh ones. The nightly job was to
call the same script as the hook, as one recorded exception to the rule that
every check lives in `.pre-commit-config.yaml`.

## Decision

- `fir-random-nightly` and `fir-fuzz` are hooks of the `manual` stage in
  `.pre-commit-config.yaml`. `.github/workflows/nightly.yml` runs them with
  `--hook-stage manual`, daily and on request. No pull request runs them.
- `fir-random-nightly` is `scripts/check-random-programs.sh --fresh 10000`,
  the script of `fir-random` with a larger budget and a new first seed, which
  it prints.
- A failure prints the seeds to replay, as
  `scripts/check-random-programs.sh SEED...`, and fails the workflow. Nothing
  files an issue.
- Each failure's seed joins `scripts/harness/regression_seeds.txt`, which
  every pull request runs. A seed names a program only for the generator of
  its day, so the failing program also joins `tests/fir/` as a test.

## Consequences

- The hooks stay in the one list, so `ci-hooks` checks them, and the exception
  is smaller than the ruling allowed: only the schedule is outside `ci.yml`.
- A bug that only fresh seeds find shows up on the next nightly run, not on
  the pull request that introduced it.
