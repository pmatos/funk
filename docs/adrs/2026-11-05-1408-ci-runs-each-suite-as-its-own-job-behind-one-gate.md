# CI runs each suite of hooks as its own job, and a gate job named pre-commit needs them all

Status: accepted; refined by ADR-2026-11-09-1645
Tier: direction; area: process

## Decision

- Every check is a hook of `.pre-commit-config.yaml`. CI runs each suite of
  hooks as its own job of `.github/workflows/ci.yml`, each its own check:
  `static`, `rust`, `lean` and `cross`. The suites run in parallel.
- One step per hook, in one form:
  `uvx pre-commit@4.6.2 run ID --all-files --verbose --show-diff-on-failure`.
  Each step runs even when one before it failed. No job sets `SKIP`.
- A gate job, `pre-commit`, needs every suite job, always runs, and passes
  only when each of them succeeded. It keeps the name of the check that the
  ruleset requires (ADR-2026-10-28-0725).
- The `ci-hooks` hook (`scripts/check_ci_hooks.py`) fails when the config,
  the workflows' steps and the gate disagree. So a new hook needs a step in
  one job, and a new job a place in the gate's `needs`. The page lists each
  case it checks.
- In CI, each test suite writes its counts to the job summary and to the log.

The human asked on 2026-11-05, in #148, for one CI job per suite, each its own
check, with each suite's counts in the job summary and the log. What each job
holds, the counts and the caches are on
[process-ci.md](../decisions/process-ci.md).

## Why

One job ran every hook, and pre-commit hides a passing hook's output. A pull
request showed one check, with no counts, and the human read it as "zero tests
running in CI". Parallel suites also make a run as long as its slowest job,
not the sum: the first run of this layout took 10 min 32 s, against 19 min
36 s for one job.

## Rejected alternatives

- **Require each suite's check in the ruleset.** Every new job would need a
  ruleset change; the gate needs none.
- **One step that loops over a job's hooks.** The step would not show which
  hook failed, and `ci-hooks` would have to parse the loop.
- **A matrix job.** Its setup steps would branch on the matrix, and its hook
  lists would reach `run` through expressions.
- **Hand the built `lean/` to `cross` as an artifact.** `cross` would wait for
  `lean`, so the run would take longer.
