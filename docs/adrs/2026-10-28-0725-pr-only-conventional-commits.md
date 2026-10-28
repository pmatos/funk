# Every change reaches main as a squash-merged PR with a Conventional Commit title

Status: accepted

## Context

Many agents commit to funk concurrently. Every change must be reviewable and
gated by CI, history on `main` must stay linear and readable, and commit
messages must be machine-readable so changelogs and releases can be generated
later.

## Decision

- A repository ruleset on `main`, versioned in `.github/rulesets/main.json`,
  requires a pull request, blocks force pushes and deletion, requires linear
  history and requires the `pre-commit` and `PR title` checks to pass. It has
  no bypass actors: nobody, including admins, pushes to `main` directly.
- PRs merge by squash only. The commit on `main` is `<PR title> (#N)` with an
  empty body, and the branch is deleted on merge.
- Commit messages and PR titles are Conventional Commits. One checker,
  `conventional-pre-commit`, runs as the local `commit-msg` hook and, in CI,
  against the PR title through the same `.pre-commit-config.yaml`.
- The PR-title workflow uses `pull_request`, not `pull_request_target`; it
  needs no secrets.

## Alternatives

- **Also lint commits pushed to `main`** (jsse does). With direct pushes
  impossible, every commit on `main` is a squash whose header is the PR title,
  which is already checked.
- **commitlint.** Stricter (header length, case, trailing full stop), but a
  second implementation in Node that could disagree with the local hook. We
  accept the looser single checker.

## Consequences

- Nobody can push to `main` or merge a PR with red checks. In an emergency the
  human edits the ruleset in GitHub settings, then restores it from the file.
- Dependabot PR titles must be conventional, so its commit prefix is `ci`.
- Apply the ruleset file with
  `gh api -X POST repos/pmatos/funk/rulesets --input .github/rulesets/main.json`;
  after editing it, update with `gh api -X PUT repos/pmatos/funk/rulesets/<id> --input …`.
