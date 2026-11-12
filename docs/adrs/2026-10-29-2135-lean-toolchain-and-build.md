# fir's Lean code is pinned to a stable Lean release, has no dependencies, and is built by one script

Status: accepted
Tier: direction; area: spec-site

## Decision

- **One pin.** `lean/lean-toolchain` names a stable Lean release, and
  `docs/spec/lean-toolchain` is a symlink to it. No nightlies and no release
  candidates. A toolchain bump is one PR. It moves the toolchain and the
  `verso` rev to the same tag through `scripts/build-spec.sh --update`, and
  never runs a bare `lake update`.
- **`lean/` is the Lake package `fir`, with no dependencies:** no Mathlib, no
  Verso and no LeanMLIR. Adding one means editing this ADR first.
- **`docs/spec/` is the Lake package `firspec`.** It requires `fir` by path
  and `verso` at the git tag named like the toolchain, and its
  `lake-manifest.json` is committed.
- **One build command.** Every Lake run in `lean/` or `docs/spec/`, in hooks,
  CI, the deployment or by hand, goes through `scripts/build-spec.sh` or
  applies both of its guards. It unsets each variable that
  `git rev-parse --local-env-vars` lists. It sets `GIT_CEILING_DIRECTORIES`
  to `lean/.lake/packages` and `docs/spec/.lake/packages`. The script also
  unsets `GH_TOKEN` and `GITHUB_TOKEN`. ADR-2026-11-05-1408 says how CI runs
  its hooks.

## Why

One pin and committed manifests make the builds reproducible. Lean, Verso
and Mathlib tag each stable Lean release with the same name, so one tag fits
all three. fir's Lean semantics needs only core Lean. In tests, Lake's git
calls inside a package clone rewrote this repository's `origin` and moved its
`HEAD`: the variables that git sets for a hook override the clone's own
repository, and a broken clone's `.git` lets git climb to this one.
Lakefiles and elaboration can run arbitrary code, so the build holds no
tokens.

## Rejected alternatives

- **Depend on Mathlib.** Nothing in the spec needs it, and it adds thousands
  of modules and a cache to keep working. It can come later at the same pin.
- **Chapters as Verso documents with `lean` code blocks.** `fir`, and
  `fir-ref` with it, would depend on Verso.
- **A nightly toolchain.** Verso and Mathlib tag stable releases, and
  nightlies are hard to reproduce.
- **`leanprover/lean-action` in CI.** A checksummed elan tarball needs no
  third-party action.
- **`GIT_CEILING_DIRECTORIES` at the repository root.** It would also stop
  git from finding this repository from `docs/spec/`.
