# Funk

Funk is a compiler toolchain. GitHub repo: **`pmatos/funk`**. Use this
owner/repo for every `gh` and GitHub MCP call.

## How this project is built

A human guides; agents build. The human sets the direction: the spec, the
roadmap, and the calls only they can make. Agents do the rest: design,
implementation, tests, docs, ADRs, reviews and PRs. Leave everything so that
the next agent, starting cold, can continue from the repository alone.

Take a question to the human only when it is a direction call that the spec,
roadmap and ADRs do not settle (label the issue `human-ready`). Within the
agreed ticket scope, how to build, test or split the work is yours to decide
and record.

## Direction questions and standing rules

- An unanswered direction question waits. Record it in a `human-ready` issue.
  Never choose an answer because a timeout expires or the human is
  unavailable. Continue work that does not depend on the answer.
- Routine implementation choices, such as naming and test details, may
  proceed within the ticket's scope and must be recorded.
- Ask the human before starting a new performance or scale ticket, or
  introducing new tooling or checking machinery, including hooks and
  verifiers. Existing authorized checks and routine implementation choices
  can proceed.

These rules apply to every agent, including orchestrators. The human approved
them in #171; ADR-2026-11-06-0744 records the decision.

## Impossible is nothing

That is our mantra. We are ambitious: we do not shy away from large amounts of
work, and we set out to achieve what looks impossible. In practice:

- Ambition means completing the agreed scope. Finish everything the ticket
  asks for. File additional work separately and obtain the human's ruling
  before widening the ticket.
- Size is never a reason to cut scope. Never call a task "too large", and never
  take "the simple road" when it gives up part of the goal.
- Large work gets a plan, not a smaller target. Break it into issues and a
  sequence of reviewable PRs, then deliver all of them.
- No stubs, placeholder implementations or "out of scope for now" to make work
  look finished. Anything left is tracked in an issue that says what remains.
- A real blocker is a contradiction in the spec, a missing direction call, or
  a technical limit you have evidence for. Name it, with what would unblock
  it. Effort is never a blocker.
- Ambition does not relax rigour: every change still passes every check below.

## Where we are going: spec, roadmap, ADRs

These are our guidelines to where we want to go. Before starting a task, read
the parts relevant to it; make sure the work moves the roadmap forward.

| Document | Path              | Answers                               |
| -------- | ----------------- | ------------------------------------- |
| Spec     | `docs/spec/`      | What funk is and must do              |
| Roadmap  | `docs/roadmap.md` | What we build next, and in what order |
| ADRs     | `docs/adrs/`      | What we decided, and why              |

- The spec and roadmap set direction, so changing them is a direction call:
  propose it in its own PR, say why, and flag it for the human.
- If your work would contradict any of the three, surface the conflict
  explicitly. Never override one silently.
- If one does not exist yet, ask the human for the direction it should give
  rather than inventing it.

## ADRs

Write an ADR in `docs/adrs/` only for a direction decision that binds more than
one module, or a future dialect or target. Its form is Decision, Why and
Rejected alternatives, in about 300 words. A proof's internal structure, an
external standard the code already follows (an ABI, IEEE 754), a choice the
next PR of the same ticket may revise, and detail that only one module needs
go in that module's doc comment or on the area page. CI warns when a PR adds
more than two ADRs. Naming, rules and template:
[`docs/adrs/README.md`](docs/adrs/README.md).

An ADR is edited in place when its decision changes; git keeps the history.
There are no refining ADRs and no `superseded` status. A deleted ADR gets a row
in [`docs/adrs/removed.json`](docs/adrs/removed.json), and every citation of it
is rewritten in the same PR. Each ADR carries a tier and an area, and
[`docs/adrs/INDEX.md`](docs/adrs/INDEX.md) lists them with what holds now and
the removed ones (ADR-2026-11-09-1610).

The area pages in [`docs/decisions/`](docs/decisions/) are the record. An agent
starting cold reads them first: each says what holds today. When a page and an
ADR disagree, the page wins, and the ADR is fixed or deleted. Each direction
rule on a page keeps one line on the main rejected alternative, and a rule the
human ruled says so, with the date. A PR that adds or changes a direction ADR
updates its area page in the same PR.

## Every change goes through a PR

A ruleset on `main` ([`.github/rulesets/main.json`](.github/rulesets/main.json))
blocks direct pushes, force pushes and deletion for everyone, the human
included. Every commit reaches `main` as the squash merge of a PR whose required
checks, `pre-commit` and `PR title`, are green.

1. Branch from an up-to-date `main`. Never commit on `main`.
2. Write commit messages as Conventional Commits; the `commit-msg` hook checks.
3. Open a PR whose title is a Conventional Commit header: squash merging makes
   it the commit message on `main`. Body: what changed and why, `Closes #N`.
4. If the PR is behind `main`, merge `main` into it, or use GitHub's "Update
   branch", and wait for its checks on the new head. The ruleset blocks a PR
   that is behind `main` from merging (ADR-2026-10-28-0725).

   `docs/adrs/INDEX.md` is generated, so never resolve a conflict in it by hand.
   Resolve and stage every other conflict first. Then run
   `python3 scripts/adr_index.py --write` and stage the result. Run earlier, the
   script writes duplicate rows for an ADR that is still unmerged.
5. Merge by squash once CI is green (auto-merge is fine). Never merge red.

Format: `type(scope)!: summary`. Types: `feat`, `fix`, `perf`, `refactor`,
`docs`, `test`, `build`, `ci`, `chore`, `style`, `revert`. `!` marks a breaking
change. Write the summary in the imperative mood, lower case, no full stop,
and keep the title under 72 characters. Rationale: ADR-2026-10-28-0725.

## Hooks and checks

Run `./scripts/ensure-hooks.sh` before anything else in a clone. Claude's
`SessionStart` hook runs it, and a `PreToolUse` gate blocks edits and shell
commands until it succeeds. Start agents in another worktree with
`./scripts/agent-session.sh --worktree <path> <agent-command> [args...]`.

- Prerequisites: `pre-commit`, `elan` (the `fir-spec` hook), `rustup`
  (the `rust-fmt`, `rust-clippy` and `rust-test` hooks; it installs the
  toolchain that `rust-toolchain.toml` pins), GNU binutils (`as` and
  `ld`) on an x86-64 Linux host, which `funk build` runs in the
  `rust-test` hook, glibc's development files (`libc.so`; `libc6-dev` on
  Debian and Ubuntu), which `funk build` links a program that calls C
  with, and valgrind (the `rust-speed` hook).
- Never bypass checks: no `--no-verify`, no `SKIP=`, no overridden
  `core.hooksPath`. If hooks cannot install or run, report why and do not
  commit until the environment is fixed.
- Run `pre-commit run --all-files` before pushing. CI runs the same hooks on
  every file, one job per suite, so a local pass predicts a CI pass
  (ADR-2026-11-05-1408). The one exception is `rust-speed`: only CI can fail
  a count over its margin (ADR-2026-11-09-1645).
- Every check lives in `.pre-commit-config.yaml`, which keeps local and CI one
  list. Add new linters and formatters there, not in a workflow, and give each
  new hook a step in one job of `.github/workflows/ci.yml`: the `ci-hooks`
  hook fails until it has one.

## File-size budget

Every text file is at most **20,000 bytes**, about 5–7k tokens of code, so any
agent can read any file whole in one pass. The `file-size-budget` hook enforces
it on commit and in CI. Rationale: ADR-2026-10-28-0724.

When a file would exceed it, split by responsibility: move a cohesive group of
functions, types, tests or doc sections into a focused sibling file or module,
keep a small entry point, and update imports, links and callers. Never minify,
cram or shorten names to fit. Only generated or vendored files may be excluded,
through the hook's `exclude` pattern.

## Unsafe Rust

`unsafe_code = "forbid"` applies to the whole workspace, and the workspace has
no unsafe code. Any unsafe Rust needs a Verus proof, and lowering `forbid`
needs a new ADR and a human ruling (ADR-2026-11-03-0808). The first unsafe code
restores the Verus tooling from the tag `verus-tooling-m0` instead of
rebuilding it (ADR-2026-11-09-1603).

## Working safely

- Kill processes only by a PID you recorded; never `pkill -9 <pattern>`, since
  patterns have matched the agent's own shell.
- Give long builds and test runs an explicit timeout up front. Never rebuild a
  binary while a test run is using it.
- Clear stale build caches before declaring that a repro still fails.

## Agent skills

- **Issue tracker:** GitHub issues on `pmatos/funk`, via `gh`; external PRs are
  not a triage surface. See [`docs/agents/issue-tracker.md`](docs/agents/issue-tracker.md).
- **Triage labels:** `needs-triage`, `needs-info`, `agent-ready`, `human-ready`,
  `wontfix`. See [`docs/agents/triage-labels.md`](docs/agents/triage-labels.md).
- **Domain docs:** `CONTEXT.md` (glossary, created lazily) and `docs/adrs/`. See
  [`docs/agents/domain.md`](docs/agents/domain.md).
