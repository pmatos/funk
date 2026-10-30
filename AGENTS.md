# Funk

Funk is a compiler toolchain. GitHub repo: **`pmatos/funk`**. Use this
owner/repo for every `gh` and GitHub MCP call.

## How this project is built

A human guides; agents build. The human sets the direction: the spec, the
roadmap, and the calls only they can make. Agents do the rest: design,
implementation, tests, docs, ADRs, reviews and PRs. Leave everything so that
the next agent, starting cold, can continue from the repository alone.

Take a question to the human only when it is a direction call that the spec,
roadmap and ADRs do not settle (label the issue `human-ready`). How to build,
test or split the work is yours to decide and record.

## Impossible is nothing

That is our mantra. We are ambitious: we do not shy away from large amounts of
work, and we set out to achieve what looks impossible. In practice:

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

Record every significant decision as an ADR in `docs/adrs/`: anything a future
agent would otherwise have to rediscover or might undo by accident. ADRs are
concise and written in clear terms: one decision each, plain words, short
sentences, no filler; most fit on one screen. Naming, rules and template:
[`docs/adrs/README.md`](docs/adrs/README.md).

## Every change goes through a PR

A ruleset on `main` ([`.github/rulesets/main.json`](.github/rulesets/main.json))
blocks direct pushes, force pushes and deletion for everyone, the human
included. Every commit reaches `main` as the squash merge of a PR whose required
checks, `pre-commit` and `PR title`, are green.

1. Branch from an up-to-date `main`. Never commit on `main`.
2. Write commit messages as Conventional Commits; the `commit-msg` hook checks.
3. Open a PR whose title is a Conventional Commit header: squash merging makes
   it the commit message on `main`. Body: what changed and why, `Closes #N`.
4. Merge by squash once CI is green (auto-merge is fine). Never merge red.

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
  toolchain that `rust-toolchain.toml` pins) and GNU binutils (`as` and
  `ld`) on an x86-64 Linux host, which `funk build` runs in the
  `rust-test` hook.
- Never bypass checks: no `--no-verify`, no `SKIP=`, no overridden
  `core.hooksPath`. If hooks cannot install or run, report why and do not
  commit until the environment is fixed.
- Run `pre-commit run --all-files` before pushing. CI runs exactly that, so a
  local pass predicts a CI pass.
- Every check lives in `.pre-commit-config.yaml`, which keeps local and CI one
  list. Add new linters and formatters there, not in a workflow.

## File-size budget

Every text file is at most **20,000 bytes**, about 5–7k tokens of code, so any
agent can read any file whole in one pass. The `file-size-budget` hook enforces
it on commit and in CI. Rationale: ADR-2026-10-28-0724.

When a file would exceed it, split by responsibility: move a cohesive group of
functions, types, tests or doc sections into a focused sibling file or module,
keep a small entry point, and update imports, links and callers. Never minify,
cram or shorten names to fit. Only generated or vendored files may be excluded,
through the hook's `exclude` pattern.

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
