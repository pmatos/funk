# Current decisions: process

This page says what holds today for how funk is built and changed. It only
summarizes the ADRs it cites. When this page and an ADR disagree, the page has
the bug (ADR-2026-11-09-1610).

## Who decides what

Every agent follows one approval boundary, orchestrators included
(ADR-2026-11-06-0744).

- An unanswered direction question waits in a `human-ready` issue. A timeout or
  the human's absence never supplies an answer. Independent work continues.
- Ambition means finishing the agreed ticket scope. Additional work is filed
  separately. The human rules before a ticket widens.
- An agent asks before starting a new performance or scale ticket.
- An agent asks before introducing new tooling or checking machinery. That
  includes hooks and verifiers.

Routine implementation choices, such as naming and test details, may proceed
within the ticket's scope. They must be recorded. Existing authorized checks can
proceed. Recording a direction choice afterward does not authorize it.
`AGENTS.md` holds these standing rules.

## The order of the milestones

M1 is "Complete the fir IR". fir is complete before the full backend starts
(ADR-2026-11-05-2255). Every backend, pass and frontend is built against the IR.
A late change to it costs the most. M1 takes fir to an IR that the frontends can
lower their sequential code to. Concurrency, exceptions and contracts arrive
through hooks M1 leaves in the format (ADR-2026-11-09-1548).

M1's scope is in `docs/roadmap.md`. The M0 close-out audit issues come first.
Then come these items:

- memory (S3);
- effect classes (H7);
- globals and external functions (H3);
- floating point (S5);
- aggregates;
- dialects and extensions (H4, H5), with a second dialect in tree.

M1 also gives the frontends what their sequential code needs
(ADR-2026-11-09-1548):

- indirect calls and function addresses;
- calls to variadic external functions;
- stack allocation;
- volatile accesses;
- `unreachable`;
- proper tail calls;
- memory intrinsics;
- inline assembly.

Each item goes through every layer at once. That includes a naive backend
lowering, so that the harness checks the item natively. Native lowering of inline
assembly waits for M4 (ADR-2026-11-09-1552). The second dialect has no lowering
to core and no native backend in M1 (ADR-2026-11-09-1545).
semantics-m1-design.md has these designs.

These stay out of M1, with a hook in the format (ADR-2026-11-09-1548):

- Defining variadic functions. The signature syntax admits them, and the verifier
  rejects a definition until the C frontend (M4) needs one.
- Concurrency (S6). The hook is the `ordering` attribute on memory ops.
- Exceptions and unwinding. A dialect may add terminators with extra successors,
  such as a call with an unwind successor.

Contract ops are also out of M1. They come as Vow's own dialect in M3
(ADR-2026-11-09-1548). C code that defines variadic functions, uses atomics or
throws cannot be lowered until M4 or later.

Vectors and structured control flow (H6) stay with the milestones that need them.
S8 stays with M2's optimizer track (ADR-2026-11-05-2255).

The later milestones are:

- M2, full x86-64 backend;
- M3, Vow frontend;
- M4, C and C++ frontend;
- M5, compile the Linux kernel;
- M6, JIT compilation;
- M7, x86 to arm64 binary translation;
- M8, WebAssembly backend, for wasm32 and wasm64, tested with wasmtime
  (ADR-2026-11-11-1450). Its number does not set the order of work.

Accepted ADRs, spike reports, issues and comments older than this numbering keep
their wording. In them, M1 to M6 mean today's M2 to M7. Living docs use the new
numbers: `docs/roadmap.md`, `README.md` and the spec's prose.

Issue #177 is the M1 epic, and the audit issues block it. Issue #164 is the M2
epic, and #177 blocks it.

## The public API

P2, the shape of funk's public API, is decided at the start of M3, before Vow
frontend work begins. It is a `human-ready` issue on M3's epic. Until then the
Rust API may change freely, and M1 and M2 do not design for API stability
(ADR-2026-11-09-1554).

## How a change reaches main

Every change reaches `main` as a squash-merged pull request
(ADR-2026-10-28-0725). A repository ruleset enforces this. It is versioned in
`.github/rulesets/main.json`.

The ruleset requires a pull request and linear history. It blocks force pushes
and deletion. It has no bypass actors, so nobody pushes to `main` directly,
admins included. In an emergency the human edits the ruleset in GitHub settings,
then restores it from the file.

The ruleset requires the `pre-commit` and `PR title` checks. It also requires a
pull request to be up to date with `main` (ADR-2026-11-03-1612). A pull request
merges only when two things are true. Its branch contains the head of `main`.
The required checks passed on the branch's own head.

A pull request that is behind `main` merges `main` into its branch, or uses
GitHub's "Update branch" button. It then waits for both checks on the new head.
So two pull requests can no longer break `main` together.

Each merge leaves every other open pull request behind, so merges happen one at
a time. Auto-merge does not update a branch. A pull request with auto-merge on
that falls behind waits until someone updates it.

The live ruleset follows the file. An edit is applied with
`gh api -X PUT repos/pmatos/funk/rulesets/<id> --input .github/rulesets/main.json`.
It is read back with `gh api repos/pmatos/funk/rulesets/26023009`. Each field the
file sets must have the file's value. The live ruleset also holds fields the
file does not set, so it never equals the file as a whole.

The commit on `main` is `<PR title> (#N)` with an empty body. The branch is
deleted on merge.

Commit messages and PR titles are Conventional Commits. One checker,
`conventional-pre-commit`, covers both, through the same
`.pre-commit-config.yaml`. It runs as the local `commit-msg` hook, and in CI
against the PR title. In CI it stays in `pr-title.yml` (ADR-2026-11-05-1408).
That workflow uses `pull_request`, not `pull_request_target`, because it needs
no secrets. Dependabot's commit prefix is `ci`, so its PR titles are
conventional.

## File size

Every text file in the repository is at most 20,000 bytes
(ADR-2026-10-28-0724). That is about 5k tokens of prose, or 5-7k tokens of code.
An agent works best on a file it can read whole.

The `file-size-budget` hook, `scripts/check_file_size.py`, enforces the cap. On
commit, pre-commit passes it the staged text files and skips binaries. CI runs
it over every file (ADR-2026-11-05-1408).

The cap is strict for every file, with no ratchet. Only generated or vendored
files are exempt, through the hook's `exclude` pattern. Authored code is never
exempt. `docs/adrs/INDEX.md` is generated, and the hook excludes it
(ADR-2026-11-09-1610).

Modules are split by responsibility from the start. When the hook fails, it
names each file and its size and says how to split.

## CI and its checks

### Suites and the gate

Every check is a hook of `.pre-commit-config.yaml`. CI runs each suite of hooks
as its own job in `.github/workflows/ci.yml` (ADR-2026-11-05-1408). Each job is
its own check. The suites run in parallel. The four jobs are:

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
  `fir-harness-test` and `coverage-matrix`. It installs both toolchains and
  binutils, and builds `lean/` again.

Each hook is one step, run with `--all-files --verbose --show-diff-on-failure`.
Each step runs even when one before it failed. `--verbose` prints a hook's
output and time when it passes. No job sets `SKIP`.

The job `pre-commit` is a gate. It needs every suite job and always runs. It
passes only when each suite job succeeded. A suite that failed, was cancelled or
was skipped fails it. It keeps the name of the required check, so a new job
needs no ruleset change.

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
the gate's `needs`. The lists above name the hooks that the ADR names. `ci.yml`
holds every step.

`fir-random-nightly` and `fir-fuzz` are hooks of the `manual` stage.
`.github/workflows/nightly.yml` runs them daily and on request, and no pull
request runs them (ADR-2026-11-08-2116). Pull requests run fixed seeds, which
keeps a local pass a prediction of a CI pass.

### Counts

When `GITHUB_STEP_SUMMARY` is set, as in CI, the test scripts write their counts
to the job summary through `scripts/suite_summary.py` (ADR-2026-11-05-1408).
They also print the counts to the log. `rust-test`, `fir-ref-test`,
`fir-round-trip`, `fir-harness` and `ci-hooks` report this way. Without the
variable, the scripts run as before.

Python test hooks report through one runner, `scripts/run_unittests.py`
(ADR-2026-11-05-1633). Its arguments are `HOOK ARGS...`, where `ARGS` are the
arguments the hook's entry gave `python`. The tests run in the runner's own process, with what `python` would
have given them: `sys.argv`, `sys.path[0]` and the `__main__` module. The runner
exits with the status their `unittest.main()` chose. It changes nothing that the
tests print.

When `GITHUB_STEP_SUMMARY` is set, the runner removes it while the tests run. It
then writes one row, titled "Python tests (HOOK)", and prints the same line to
the log. So a test that needs the variable has to set it itself. A new Python
test hook should call the runner the same way. The runner's own tests are in the
hook `run-unittests-test`, in the `static` job.

### Caches

Each job that has hooks with environments caches `~/.cache/pre-commit` under its
own key (ADR-2026-11-05-1408). The `rust` job saves the Rust toolchain, and
`cross` restores it.

`cross` and `pages.yml` copy the `lean` job's Lean setup steps. The copies are
four steps, without the save (ADR-2026-11-05-1954). Comments say to change all
the copies together.

CI caches each of its two installer downloads: `rustup-init` and `elan.tar.gz`
(ADR-2026-11-05-1954). Each cache holds only the downloaded file
in `RUNNER_TEMP`. The key is `<tool>-installer-<os>-<version>-<sha256>`, so a
bump of either pin is a miss.

The pins stay in the workflow, twice in each copy. They are in the `env` of the
step `Restore the <tool> installer` and of the step `Install <tool>`. A bump
edits both.

`scripts/ci-install.sh rustup|elan` runs each install step. It downloads
the installer only when the restore step found no copy. It checks the file
against its SHA-256 on every run, hit or miss, before using it. A cached file
that fails fails the step on every run. That lasts until a bump changes the key
or the cache entry is deleted.

One job saves each cache: `rust` saves the rustup installer, and `lean` saves
elan's. `cross` and `pages.yml` only restore. A save step runs only
on a miss and only when its install step passed. So the cache holds only a file
that passed its check. `pages.yml` deploys, so it never saves a cache.

## ADRs

### Tier, area, index and pages

Every ADR ends its status paragraph with one line, `Tier: TIER; area: AREA`
(ADR-2026-11-09-1610). This line is metadata, so adding or correcting it does
not break immutability.

The tier follows one test:

- `direction` says what fir is, or sets a rule that every change follows. A
  change to another module or tool would be bound by it.
- `implementation` says how one tool does one thing.

The area is one of nine: `semantics`, `text-format`, `validation`, `fir-ref`,
`rust-ir-and-tools`, `x86-64-backend`, `testing-and-harness`, `spec-site` and
`process`. An ADR that spans areas sits where a reader would look for it.

`scripts/adr_index.py --write` generates `docs/adrs/INDEX.md`. It has one line
per ADR: tier, area, title and what holds now. What holds now is the ADR and
every ADR that its `refined by` and `extended by` links reach. A superseded ADR
shows what holds of its successor. The `adr-index` hook fails when the index is
stale or an ADR has no tier and area.

`docs/decisions/` holds one page per area in plain prose, each citing the ADRs
it rests on. A page that outgrows the file-size budget continues in a sibling,
`AREA-TOPIC.md`. ADRs stay immutable, and the pages only summarize them. The
index links each ADR to its page. The hook also fails when no page of an
accepted ADR's own area cites it.

Implementation detail that only one module needs goes in that module's doc
comment, not in a new ADR. `docs/adrs/README.md` says how to decide.

### ADR ids

An ADR is named `YYYY-MM-DD-HHMM-slug.md`, with the UTC time it was written
(ADR-2026-10-30-1329). When an ADR already holds that minute, the newer one adds
the seconds: `YYYY-MM-DD-HHMMSS-slug.md`. An ADR's id is its whole timestamp, so
the minute form and the seconds form are two ids.

The `adr-ids` hook, `scripts/check_adr_ids.py`, fails on a name that does not
have one of the two forms. It needs ASCII digits, a real date and time, and a
slug of lower-case words joined by hyphens. It also fails when two files share
an id, and names every file with that id.

The hook does not take pre-commit's file list. So a commit that adds one ADR is
still checked against the ADRs already on `main`. It reads git's index, not the
directory, so untracked files do not fail a commit. It cannot tell which ADR is
newer, so it accepts either form. Review keeps the seconds form for a taken
minute. `adr-ids-test` runs the hook's tests in `scripts/test_check_adr_ids.py`.

Two pull requests cannot merge a clash. The second one falls behind, updates,
and fails `adr-ids` before it merges (ADR-2026-11-03-1612).

A minute-form id is a prefix of a seconds-form id of the same minute. A search
for a citation must stop at the end of the digits.

### ADR citations

The `adr-citations` hook, `scripts/check_adr_citations.py`, checks ADR citations
in every tracked text file (ADR-2026-11-05-1709). A text file here is UTF-8,
holds no NUL byte and is not a symbolic link. The hook runs on every commit.
Deleting or renaming an ADR breaks citations in files the commit does not touch.
CI runs it with `--all-files`.

The hook ports the grammar of the spec checker, which is
`docs/spec/FirSpecSite/Citation.lean`. The spec build still checks citations in
its own sources (ADR-2026-10-30-1439).

A citation ends at its last digit, so it matches a whole id. Four or six digits
after the date are an id, and any other number is malformed. A placeholder is
not a citation. Code spans and fenced code blocks are blanked first, because
code is quoted, not cited.

`docs/spec/FirSpecSite/citation-cases.json` is one table of cases. The spec's
tests and the hook's tests both read it. A change to either grammar adds a case
there, which both must pass.

`FIXTURES` in the script lists, each with a reason, the files whose bad citations
are test data on purpose. Those files are not checked. A listed file that git
does not track, or that cites no missing ADR, fails the hook. `adr-citations-test`
runs the hook's tests. Both hooks have a step in the `static` job.
