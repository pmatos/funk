# A pull request merges only when it is up to date with main

Status: accepted

## Context

The ruleset on `main` (ADR-2026-10-28-0725) requires the `pre-commit` and
`PR title` checks, but sets `strict_required_status_checks_policy` to
`false`. CI runs on a pull request's merge with `main` as `main` was when
the checks ran. Once `main` moves, those checks no longer describe what the
merge produces. So two pull requests that each pass alone can merge one
after the other and break `main` together. ADR-2026-10-30-1329 names this
gap for ADR ids, and parallel pull requests do collide: #108 and #110 were
open at once, and each named an ADR for the minute 2026-11-03 01:07. #110
gave its ADR the seconds before either merged, but no check would have
stopped both from merging with green checks.

A merge queue would test each pull request on top of the ones ahead of it,
but GitHub offers merge queues only to repositories that an organization
owns, and a user owns `pmatos/funk`.

## Decision

- `.github/rulesets/main.json` sets `strict_required_status_checks_policy`
  to `true`. GitHub then merges a pull request only when its branch
  contains the head of `main` and the required checks passed on the
  branch's own head.
- A pull request that is behind `main` merges `main` into its branch, or
  uses GitHub's "Update branch" button, and waits for both checks on the
  new head before it merges.
- The live ruleset follows the file. After the pull request that brings
  this ADR merges, it is updated with the `gh api -X PUT` command that
  ADR-2026-10-28-0725 gives, and read back with
  `gh api repos/pmatos/funk/rulesets/<id>` to confirm it matches.

## Alternatives

- **A merge queue.** Not available to a repository owned by a user.
- **Keep the policy off and rely on CI on `main`.** A clash is found only
  after it lands, and every later pull request fails until someone fixes
  `main`.

## Consequences

- The checks that pass on a pull request ran on the tree its squash merge
  puts on `main`, so two pull requests can no longer break `main` together.
- Each merge leaves every other open pull request behind. Each one then
  updates and runs CI again before it merges, so merges happen one at a
  time, and a CI run, with its Lean and Rust builds, is the wait between
  them.
- Auto-merge does not update a branch. A pull request with auto-merge on
  that falls behind waits until someone updates it.
