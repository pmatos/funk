# Every change reaches main as a squash-merged PR with a Conventional Commit title, up to date with main

Status: accepted
Tier: direction; area: process

## Decision

- A repository ruleset on `main`, versioned in `.github/rulesets/main.json`,
  requires a pull request, blocks force pushes and deletion, requires linear
  history and requires the `pre-commit` and `PR title` checks to pass. It has
  no bypass actors: nobody, admins included, pushes to `main` directly. In an
  emergency the human edits the ruleset in GitHub settings, then restores it
  from the file.
- The ruleset sets `strict_required_status_checks_policy` to `true`. A pull
  request merges only when its branch contains the head of `main` and the
  required checks passed on the branch's own head. A pull request that is
  behind merges `main` into its branch, or uses GitHub's "Update branch", and
  waits for both checks on the new head.
- The live ruleset follows the file. It was created with
  `gh api -X POST repos/pmatos/funk/rulesets --input .github/rulesets/main.json`.
  An edit is applied with
  `gh api -X PUT repos/pmatos/funk/rulesets/<id> --input .github/rulesets/main.json`
  and read back: each field the file sets must have the file's value.
- PRs merge by squash only. The commit on `main` is `<PR title> (#N)` with an
  empty body, and the branch is deleted on merge.
- Commit messages and PR titles are Conventional Commits. One checker,
  `conventional-pre-commit`, runs as the local `commit-msg` hook and, in CI,
  against the PR title, through the same `.pre-commit-config.yaml`. The
  PR-title workflow uses `pull_request`, not `pull_request_target`; it needs
  no secrets. Dependabot's commit prefix is `ci`.

The human set the PR rules on 2026-10-28 in #2, and ruled on 2026-11-03 in
#121 that a pull request is up to date with `main` before it merges.

## Why

Many agents commit to funk at once. Every change must be reviewable and gated
by CI, history on `main` must stay linear and readable, and commit messages
must be machine-readable. Checks that ran on an older `main` no longer
describe what a merge produces: two pull requests that each pass alone can
break `main` together. #108 and #110 were open at once with ADRs for the same
minute.

## Rejected alternatives

- **A merge queue.** GitHub offers one only to repositories that an
  organization owns, and a user owns `pmatos/funk`.
- **Up-to-date policy off, relying on CI on `main`.** A clash is found only
  after it lands, and every later pull request fails until `main` is fixed.
- **Also lint commits pushed to `main`.** Every commit on `main` is a squash
  whose header is the PR title, which is already checked.
- **commitlint.** Stricter, but a second implementation in Node that could
  disagree with the local hook.
