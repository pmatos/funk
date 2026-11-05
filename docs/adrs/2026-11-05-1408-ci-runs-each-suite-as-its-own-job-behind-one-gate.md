# CI runs each suite of hooks as its own job, and a gate job named pre-commit needs them all

Status: accepted

## Context

Every check is a hook of `.pre-commit-config.yaml`, and CI ran them all in
one job, `pre-commit`, with `pre-commit run --all-files`. The ruleset of
`main` requires the checks `pre-commit` and `PR title`
(ADR-2026-10-28-0725, ADR-2026-11-03-1612).

pre-commit hides the output of a hook that passes. The log said only
`Rust tests pass (cargo test)....Passed`, with no counts, and a pull
request showed one check for every suite. On 2026-11-05 the human read
this as "zero tests running in CI", and asked in
[#148](https://github.com/pmatos/funk/issues/148) for both: one CI job per
suite, each its own check on a pull request, and each suite's counts in
the job summary and in the log.

Facts:

- `pre-commit run` takes one hook id at a time.
- A job's `needs` names jobs of its own workflow only.
- The single job took 19 min 36 s on run 42035177701; its hooks took
  18 min 51 s. `fir-spec` took 11 min 27 s, `fir-harness` 2 min 27 s,
  `fir-ref-test` 1 min 46 s, `rust-test` 1 min 29 s and `verus-proof`
  1 min 9 s; the other 33 hooks took about half a minute together.

## Decision

- **Four suite jobs in `.github/workflows/ci.yml`**, each its own check:
  - `static`, "Static checks": `file-size-budget`, `hidden-chars`,
    `adr-ids`, `adr-ids-test`, `g0`, `g0-test`, `ci-hooks`,
    `ci-hooks-test`, `suite-summary-test`, the hooks of pre-commit-hooks,
    `typos`, `ruff-check`, `ruff-format`, `shellcheck`, `actionlint` and
    `zizmor`. Only the `zizmor` step holds `GH_TOKEN`.
  - `rust`, "Rust suite": `rust-fmt`, `rust-clippy`, `rust-test`,
    `verus-proof`, `verus-report-test`, `unsafe-code` and
    `unsafe-code-test`. It installs rustup, the pinned Rust toolchain,
    Verus and GNU binutils.
  - `lean`, "Lean suite": `fir-spec` and `fir-ref-test`. It installs elan
    and the pinned Lean toolchain, restores the Verso build, and is the one
    job that saves it.
  - `cross`, "Cross-language suite": `fir-round-trip`, `fir-harness`,
    `fir-harness-test` and `coverage-matrix`. It installs both toolchains
    and binutils, and builds `lean/` again, beside the `lean` job.

  `conventional-pre-commit`, a `commit-msg` hook, stays in `pr-title.yml`.
- **One step per hook**, in one form:
  `uvx pre-commit@4.6.2 run ID --all-files --verbose --show-diff-on-failure`.
  Each step runs even when one before it failed, as `--all-files` ran every
  hook. `--verbose` prints a hook's output and time when it passes. No job
  sets `SKIP`.
- **A gate.** The job `pre-commit` needs every suite job, always runs, and
  passes only when each of them succeeded: a suite that failed, was
  cancelled or was skipped fails it. It keeps the required check's name,
  so the ruleset does not change.
- **The `ci-hooks` hook** (`scripts/check_ci_hooks.py`) reads the config
  and every workflow. It fails when a hook runs in no step or in more than
  one, when a hook of the `pre-commit` stage runs outside `ci.yml` (whose
  jobs the gate needs), when a step runs an id that is not a hook or no
  id, when a hook runs without `--all-files` (a hook of other stages:
  without its `--hook-stage`), when anything sets `SKIP`, and when the gate
  does not need every other job of `ci.yml` or does not always run.
- **Counts.** When `GITHUB_STEP_SUMMARY` is set, as in CI, the test scripts
  write their counts to the job summary through `scripts/suite_summary.py`
  and print them to the log:
  - `rust-test`: test runs (one per `test result:` line of `cargo test`),
    tests run, passed, failed and ignored.
  - `fir-ref-test`: for each Lean library, the `#guard`, `#guard_msgs`,
    `theorem` and `example` commands that building `lean/` checked,
    counted in the sources without comments and literals; and the
    canonical texts reprinted, the non-canonical texts printed as their
    canonical sibling, and the texts that `fir-ref validate` accepts.
  - `fir-round-trip`: the texts that Rust printed, from `tests/fir/` and
    from the generator, each reprinted and accepted.
  - `fir-harness`: the harness's checks, passed, failed and invalid, and
    its check on the invalid-verdict fixture.
  - `ci-hooks`: the hooks of each job.

  Without `GITHUB_STEP_SUMMARY`, the scripts run as before.
- **Caches.** Each job that has hooks with environments caches
  `~/.cache/pre-commit` under its own key, since it installs only its own
  hooks'. The `rust` job saves the Rust toolchain and `cross` restores it.
  `cross` and `pages.yml` copy the `lean` job's three Lean setup steps.

## Alternatives

- **Require each suite's check in the ruleset.** Every new job would then
  need a ruleset change; the gate needs none.
- **One step that loops over a job's hooks.** Shorter, but the step would
  not show which hook failed, and `ci-hooks` would have to parse the loop.
- **A matrix job.** Its setup steps would branch on the matrix, and its
  lists of hooks would reach `run` through expressions.
- **Hand the built `lean/` to `cross` as an artifact.** `cross` would wait
  for `lean`, so the run would take longer. Caching `lean/.lake` across
  runs would let a cache hit skip the `#guard` checks.
- **Python test counts in the summary.** The Python test hooks run
  `unittest` from their `entry`, so their counts ("Ran N tests") reach the
  log through `--verbose`, but not the summary: that needs a changed hook
  entry or test, or step logic outside pre-commit, which #150 leaves to the
  human.

## Consequences

- A pull request shows each suite as its own check, and the job summary
  lists the counts.
- The suites run in parallel: a run takes as long as its slowest job, not
  the sum of the suites. The first run of this layout, 42044135666, took
  10 min 32 s: `lean` 10 min 23 s, `cross` 5 min 57 s, `rust` 3 min 14 s
  and `static` 1 min 13 s.
- `lean/` is built twice per run, and toolchains are restored in more than
  one job, so a run uses more runner minutes.
- A new hook needs a step in one job of `ci.yml`, and a new job a place in
  the gate's `needs`; `ci-hooks` fails until both are there.
- `--verbose` makes the logs long: they hold the output of `cargo test`,
  the Lean build and the harness.
- This refines ADR-2026-10-28-0724, ADR-2026-10-30-1329 and
  ADR-2026-10-30-1250, which say that CI runs `pre-commit run --all-files`;
  ADR-2026-10-29-2135, ADR-2026-10-30-1030, ADR-2026-11-03-0809,
  ADR-2026-10-30-1229 and ADR-2026-10-30-2049, which say that the CI job
  installs elan, Rust, Verus and binutils: the suite jobs install them now;
  and ADR-2026-10-30-1031, whose `pages.yml` copies the Lean setup steps of
  `ci.yml`: `ci.yml` now holds two copies, in the `lean` and `cross` jobs,
  and the comments say to change all three together.
