# Current decisions: CI and its checks

This page continues [process.md](process.md). It says how CI runs funk's checks,
how the suites report their counts, and what CI caches. It is the record: when
this page and an ADR disagree, the page wins, and the ADR is fixed or deleted
(ADR-2026-11-09-1610).

## Suites and the gate

Every check is a hook of `.pre-commit-config.yaml`. CI runs each suite of hooks
as its own job in `.github/workflows/ci.yml` (ADR-2026-11-05-1408). Each job is
its own check. The suites run in parallel, so a run takes as long as its slowest
job. The human asked for this on 2026-11-05, in #148: one CI job per suite, each
its own check, with each suite's counts in the job summary and in the log. The
four jobs are:

- `static`, "Static checks". Its hooks include `file-size-budget`, `adr-ids`,
  `g0` and `ci-hooks`. They also include `typos`, `ruff-check`, `shellcheck`,
  `actionlint` and `zizmor`. Only the `zizmor` step holds `GH_TOKEN`.
- `rust`, "Rust suite". It holds `rust-fmt`, `rust-clippy`, `rust-test`,
  `rust-speed` and `rust-speed-test`. It installs rustup, the pinned Rust
  toolchain, GNU binutils and valgrind.
- `lean`, "Lean suite". It holds `fir-spec` and `fir-ref-test`. It installs elan
  and the pinned Lean toolchain. It restores the Verso build and is the one job
  that saves it.
- `cross`, "Cross-language suite". It holds `fir-round-trip`, `fir-harness`,
  `fir-random`, `fir-harness-test` and `coverage-matrix`. It installs both
  toolchains and binutils, and builds `lean/` again, beside the `lean` job.

`conventional-pre-commit`, a `commit-msg` hook, runs in `pr-title.yml` instead
([process.md](process.md#how-a-change-reaches-main)).

Rejected: one job that runs every hook. pre-commit hides a passing hook's
output, so a pull request showed one check and no counts. Rejected: handing the
built `lean/` to `cross` as an artifact. `cross` would wait for `lean`, and the
run would take longer.

Each hook is one step, which runs
`uvx pre-commit@4.6.2 run ID --all-files --verbose --show-diff-on-failure`.
Each step runs even when one before it failed. `--verbose` prints a hook's
output and time when it passes. No job sets `SKIP`.

Rejected: one step that loops over a job's hooks. The step would not show which
hook failed, and `ci-hooks` would have to parse the loop. Rejected: a matrix
job. Its setup steps would branch on the matrix, and its hook lists would reach
`run` through expressions.

The job `pre-commit` is a gate. It needs every suite job and always runs. It
passes only when each suite job succeeded. A suite that failed, was cancelled or
was skipped fails it. It keeps the name of the required check, so a new job
needs no ruleset change.

Rejected: requiring each suite's check in the ruleset. Every new job would then
need a ruleset change.

The `ci-hooks` hook, `scripts/check_ci_hooks.py`, reads the config and every
workflow. It fails in each of these cases:

- a hook runs in no step, or in more than one;
- a hook of the `pre-commit` stage runs outside `ci.yml`;
- a step runs an id that is not a hook, or no id;
- a hook runs without `--all-files`;
- a hook of another stage runs without its `--hook-stage`;
- anything sets `SKIP`;
- the gate does not need every other job of `ci.yml`, or does not always run.

So a new hook needs a step in one job of `ci.yml`. A new job needs a place in
the gate's `needs`. The lists above name some of each job's hooks. `ci.yml`
holds every step.

`lean/` is built twice per run, and toolchains are restored in more than one
job, so a run uses more runner minutes than one job did. On a pull request both
builds start from `main`'s ([Lean builds](#lean-builds)). `--verbose` makes the
logs long: they hold the output of `cargo test`, the Lean build and the harness.

`fir-random-nightly` and `fir-fuzz` are hooks of the `manual` stage.
`.github/workflows/nightly.yml` runs them daily and on request, and no pull
request runs them (ADR-2026-11-08-2116). Pull requests run fixed seeds, which
keeps a local pass a prediction of a CI pass.

## Counts

When `GITHUB_STEP_SUMMARY` is set, as in CI, the test scripts write their counts
to the job summary through `scripts/suite_summary.py` (ADR-2026-11-05-1408).
They also print the counts to the log. Without the variable, the scripts run as
before. The hooks that report this way, and what they count:

- `rust-test`: test runs (one per `test result:` line of `cargo test`), tests
  run, passed, failed and ignored.
- `fir-ref-test`: for each Lean library, the `#guard`, `#guard_msgs`, `theorem`
  and `example` commands that building `lean/` checked, counted in the sources
  without comments and literals; the canonical texts reprinted, the
  non-canonical texts printed as their canonical sibling, and the texts that
  `fir-ref validate` accepts.
- `fir-round-trip`: the texts that Rust printed, from `tests/fir/` and from the
  generator, each reprinted and accepted.
- `fir-harness`: the harness's checks, passed, failed and invalid, and its
  check on the invalid-verdict fixture.
- `ci-hooks`: the hooks of each job.

### The Python test runner

Python test hooks report through one runner, `scripts/run_unittests.py`. The
human chose it on 2026-11-05, in #150: one shared runner that the hooks'
entries call, with no change to any test file. Its arguments are
`HOOK ARGS...`, where `ARGS` are the arguments the hook's entry gave `python`:
a test file, or `-m unittest` and its arguments. Each such entry puts
`scripts/run_unittests.py HOOK` after `python` and keeps the rest.

The tests run in the runner's own process, with what `python` would have given
them: `sys.argv`, `sys.path[0]` and the `__main__` module. The runner exits with
the status their `unittest.main()` chose. When a test file does not import or
does not exist, it exits with 1 or 2, as `python FILE` does. It changes nothing
that the tests print.

When `GITHUB_STEP_SUMMARY` is set, the runner removes it while the tests run, so
nothing they run writes to the summary. It then writes one row, titled "Python
tests (HOOK)": tests run, passed, failed, errors and skipped, expected failures
and unexpected successes when there are any, and the exit status when it is
not 0. When the tests do not run at all, the row says why. It prints the same
line to the log. So a test that needs the variable has to set it itself.

A new Python test hook calls the runner the same way, so that its counts reach
the summary, and also runs when `scripts/run_unittests.py` changes. The
runner's own tests, `scripts/test_run_unittests.py`, run each kind of test
module both the old way and through the runner, and compare the exit status,
the output and what the tests see. They are the hook `run-unittests-test`, in
the `static` job.

Rejected: each test file writes its own counts. Every test file would repeat
the same code, and the human ruled out test changes. Rejected: steps in
`ci.yml` that read the log. Logic would leave `.pre-commit-config.yaml`, which
keeps local and CI one list of checks. Rejected: running the old entry in a
child process and reading its `Ran N tests` line, which holds no count of the
tests that passed.

## Caches

Each job that has hooks with environments caches `~/.cache/pre-commit` under its
own key, since it installs only its own hooks' (ADR-2026-11-05-1408). The `rust`
job saves the Rust toolchain, and `cross` restores it.

`cross` and `pages.yml` copy the `lean` job's Lean setup steps. The copies are
four steps, without the save. Comments say to change all the copies together.

### Lean builds

On a pull request, the `lean` and `cross` jobs restore `lean/.lake/build` and
`docs/spec/.lake/build` as `main` last built them, and Lake rebuilds what
changed (ADR-2026-11-12-1430). A push to `main` restores neither and builds
both packages from scratch, so every merge is checked from scratch. The human
approved this performance ticket on 2026-11-09, in #275.

- One entry holds both directories. Only the `lean` job saves it, only on
  `main` and only when every hook of the job passed. Its key is
  `lean-build-<os>-<hash>-<commit>`, where the hash covers `lean/lean-toolchain`,
  `lean/lake*` and `docs/spec/lake*`.
- The restore step's key and restore key are both `lean-build-<os>-<hash>-`, so
  a pull request gets the newest entry of `main` with the same toolchain and
  lakefiles, and a change to either builds from scratch. On `main` the step
  only looks the key up, with `lookup-only`, and the save step reuses its key.
- `cross` runs the same step through a YAML anchor, `*lean-build`, so the two
  cannot drift. It also downloads `docs/spec/`'s build, which it does not use.
- A pull request never saves: GitHub scopes its entries to it, and they would
  fill the cache. `pages.yml` deploys and builds from scratch.

A hit trusts Lake's traces. A module whose source, imports, toolchain, options
and declared inputs are unchanged keeps `main`'s result, so its `#guard`s and
theorems do not run again; `--wfail` still fails on its replayed warnings. Lake
sees no other read at elaboration, so each one is declared: the `.cases` files
and `citation-cases.json` as `input_file`s, `lean/Fir` for `{includeLiterate}`
as an `input_dir`, and the list of `lean/`'s `.lean` files that
`#check_axioms` walks as the target `sourcePaths`
([spec-site-lean-build.md](spec-site-lean-build.md#what-lean-code-in-lean-may-not-do)).
Code that adds a read at elaboration, of a file, a directory, the environment
or the clock, declares it in the same PR. `firspec` reads the ADRs and
`FIRSPEC_COMMIT` when it renders, which runs on every build.

Measured on 2026-11-12 on a 4-core machine, where clean builds of `lean/` and
of `docs/spec/` with Verso took about 14 minutes each: both build
directories restored onto a fresh checkout make each `lake build` a no-op in
about 1 s, and rendering the document still takes 2 minutes. Editing
`FirTest.PrintParse` rebuilds only it, and a stray `.lean` file reruns only
`FirCheck`. An entry is about 1.5 GB on disk and 210 MB compressed. GitHub
evicts the least recently used entries past 10 GB, and every run restores the
toolchain and Verso entry, so older `lean-build-` entries go first.

Rejected: no cache, which rebuilt both packages on every run, also when a pull
request touched neither. Rejected: one entry per package, which doubles the
entries and the steps. Rejected: tracing the file list for all of `FirTest`,
which would rebuild every test module when a file is added.

### Installer downloads

CI caches each of its two installer downloads: `rustup-init` and `elan.tar.gz`.
The human asked on 2026-11-05, in #160, for the installer downloads to be
cached, so that a run downloads one only on a cache miss. Each cache holds only
the downloaded file in `RUNNER_TEMP`. The key is
`<tool>-installer-<os>-<version>-<sha256>`, so a bump of either pin is a miss.

The pins stay in the workflow, twice in each copy. They are in the `env` of the
step `Restore the <tool> installer`, for the key, and of the step
`Install <tool>` right after it. A bump edits both.

Rejected: the pins in the job's `env`, read by both steps. Every later step of
the job, the toolchain installs and the hooks included, would see them.

`scripts/ci-install.sh rustup|elan` runs each install step. It downloads
the installer only when the restore step found no copy, with retries. It checks
the file against its SHA-256 on every run, hit or miss, before using it. A
cached file that fails fails the step on every run. That lasts until a bump
changes the key or the cache entry is deleted. The script also keeps `ci.yml`
within its budget and holds one copy of each download command.

Rejected: the download kept inline in each step. `ci.yml` would pass 20,000
bytes.

One job saves each cache: `rust` saves the rustup installer, and `lean` saves
elan's. These are the jobs that already save the Rust and Lean toolchains.
`cross` and `pages.yml` only restore, with `actions/cache/restore`. A save step
runs only on a miss and only when its install step passed. So the cache holds
only a file that passed its check. One saver per key means that two jobs of one
run never race to save it. `pages.yml` deploys, so it never saves a cache.

Rejected: `actions/cache` in every job, restoring and saving at the end of the
job. The jobs that share a key would race to save it, and `pages.yml` would
save.

A warm run downloads neither installer. A run after a bump, or the first on a
pull request when `main` has no cache yet, downloads in each job that misses,
`cross` included when it reaches the step before `rust` or `lean` has saved.
The toolchain installs, `apt-get`, `uvx` and Lake's fetches are not cached this
way.
