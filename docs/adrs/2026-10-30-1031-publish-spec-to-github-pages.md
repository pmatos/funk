# The rendered spec is published to GitHub Pages from every push to main

Status: accepted

## Context

The spec is literate Lean, rendered with Verso (ADR-2026-10-29-2015). The
rendered document is a build output and is not committed. CI builds it on
every PR through the `fir-spec` pre-commit hook, but until now nothing
published it, so reading it meant building it. On 2026-10-29 the human asked
for the rendered spec to be published to GitHub Pages on every push to
`main`, including enabling Pages and setting the repository homepage
([#28](https://github.com/pmatos/funk/issues/28)).

Lakefiles and elaboration run arbitrary code, so the build is guarded and
holds no tokens (ADR-2026-10-29-2135). A Pages deployment needs
`pages: write` and an OIDC token.

## Decision

- **Every push to `main` deploys.** `.github/workflows/pages.yml` runs on
  each push to `main`, and by hand through `workflow_dispatch`. Both its jobs
  run only for `refs/heads/main`, and the `github-pages` environment accepts
  deployments only from `main`. Pull requests never deploy; their CI still
  builds the document through the hook.
- **Same build as CI.** The `build` job installs elan, restores the cache
  and installs the pinned toolchain with a copy of the three steps in
  `ci.yml`; a comment in each file says to change both together. It then
  runs `scripts/build-spec.sh OUT`, the script the hook runs, and deploys
  `OUT/html-multi`. Every Lake run goes through the script and its guards.
- **Through Actions artifacts.** The `build` job uploads the site with
  `actions/upload-pages-artifact`, and the `deploy` job publishes it with
  `actions/deploy-pages`. No HTML is committed, and no branch is written.
- **Least privilege.** The `build` job may only read the repository; it has
  no write permission and no OIDC token. Only the `deploy` job, which runs no
  code from the repository, has `pages: write` and `id-token: write`.
- **One run at a time.** The concurrency group `pages-<ref>` runs one run per
  ref and never cancels one half way. A newer push replaces a run that is
  still waiting, so `main` deploys its latest commit and may skip the ones
  between. A failed build skips the deploy, so the previous site stays up.
- **No cached document.** The workflow restores the toolchain and
  `docs/spec/.lake/packages` from the cache that `ci.yml` saves, with the
  same key, and never saves a cache itself. `docs/spec/.lake/build` is never
  cached, so the document is rebuilt from its sources.
- **Every page names its commit** (ADR-2026-10-30-1046).
- **Easy to find.** The site is <https://p.ocmatos.com/funk/>: the
  repository's Pages site, under the custom domain of the owner's user site.
  It is the repository's homepage, and `docs/spec/README.md` links to it.

## Alternatives

- **Commit the HTML to a `gh-pages` branch.** ADR-2026-10-29-2015 keeps build
  output out of git, and pushing a branch needs `contents: write` in the job
  that runs Lake.
- **Deploy from the `pre-commit` job of `ci.yml`.** That job runs every hook
  with a token for zizmor's online audits; deploy rights do not belong there.
- **Upload the document from `ci.yml` and deploy it on `workflow_run`.** It
  saves the second build, but `workflow_run` is a privileged trigger that
  zizmor flags. The deploy would also publish what a job holding a token
  produced, and depend on a second workflow's artifact. With a warm cache
  the second build costs only the document.
- **Share the three setup steps through a composite action** in
  `.github/actions/`. zizmor's `self-repository` audit then asks for
  `uses: $/...`, which actionlint `v1.7.12`, the newest release, rejects, and
  its `github-env` audit flags the `GITHUB_PATH` write inside the action.
  Passing both linters would need an ignore rule or a linter change.

## Consequences

- Readers follow the spec as it changes without building it.
- Each push to `main` builds the document twice, once in CI and once to
  deploy. With a warm cache this costs the document build, not Verso's.
- The first deploy after a toolchain bump builds Verso when `ci.yml` on
  `main` has not yet saved the new cache.
- A bump of elan, or a change to the cache's paths or key, edits both
  `ci.yml` and `pages.yml`. If the keys drift, the deploy still works but
  builds Verso every time.
- The site's URL follows the owner's user-site domain. If that domain
  changes, the homepage and the README link change with it.
