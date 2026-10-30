# Every rendered page of the spec names the commit it was built from

Status: accepted

## Context

The rendered spec is published from every push to `main`
(ADR-2026-10-30-1031). Readers need to know how current a page is, and a
local build should not pass for a published one.

`scripts/build-spec.sh` renders the document for the `fir-spec` hook, for CI
and for the deployment (ADR-2026-10-29-2135). Lake rebuilds on changed files,
not on a changed environment, so a commit read while Lean elaborates the
document goes stale in a warm local build. Verso does not clean its output
directory, so pages of a renamed chapter stay there. Verso's
`HtmlConfig.extraContents` adds the same elements to every page.

## Decision

- `scripts/build-spec.sh` reads the commit with `git rev-parse HEAD`.
  `actions/checkout` leaves `HEAD` at `GITHUB_SHA`, so CI and the deployment
  need no input of their own, and the hook's command is unchanged.
- When `git status --porcelain` lists anything, untracked files included, the
  script adds `-dirty` to the commit. It runs git with
  `--no-optional-locks`, because a hook runs while git holds the index.
- The script passes the first 12 hex digits, plus any `-dirty`, to
  `lake exe firspec` in `FIRSPEC_COMMIT`. When `GITHUB_SERVER_URL` and
  `GITHUB_REPOSITORY` are set, as in Actions, it also passes the commit's
  page on GitHub in `FIRSPEC_COMMIT_URL`.
- `docs/spec/FirSpecMain.lean` reads both variables when it renders, and adds
  "Built from commit …" to every page through `extraContents`, linked when
  there is a URL. When `FIRSPEC_COMMIT` is unset, pages carry no line.

## Alternatives

- **Read the commit while Lean elaborates the document.** A warm local build
  would show the commit of the last full build.
- **Edit the rendered HTML after `lake exe firspec`.** It depends on Verso's
  internal markup, and stale pages in the output directory would need
  clearing first.
- **Pass `GITHUB_SHA` into the script.** It equals `HEAD` after checkout, and
  a second source of the commit would skip the `-dirty` check in CI.

## Consequences

- A page says how current it is, and a link takes the reader to the commit.
- A build in the hook of a commit is `-dirty`, because that commit does
  not exist yet. A CI build is `-dirty` when an earlier hook changed a file.
- Rendering depends on two environment variables. A bare `lake exe firspec`
  renders pages without the line.
