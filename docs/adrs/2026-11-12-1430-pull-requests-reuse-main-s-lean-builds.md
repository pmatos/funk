# Pull requests reuse main's Lean builds, and main builds them from scratch

Status: accepted
Tier: direction; area: process

## Decision

- On a pull request, the `lean` and `cross` jobs of `ci.yml` restore
  `lean/.lake/build` and `docs/spec/.lake/build` from the newest entry that
  `main` saved, and Lake rebuilds what changed. A pull request never saves.
- A push to `main` restores neither, builds both packages from scratch and,
  when every hook of the `lean` job passed, saves one entry,
  `lean-build-<os>-<hash>-<commit>`. The hash covers `lean/lean-toolchain` and
  both packages' lakefiles and manifests. `pages.yml` builds from scratch.
- A hit trusts Lake. Lake rebuilds a module when its source, an import, the
  toolchain, its options or a declared input changes. Otherwise the module's
  checks, `#guard` and theorems alike, are those of `main`'s clean build, and
  `--wfail` still fails on its replayed warnings.
- So anything that elaboration reads is a Lake input. Today these are the
  `.cases` files and `citation-cases.json` (`input_file`), `lean/Fir` for
  `{includeLiterate}` (`input_dir`), and the list of `lean/`'s `.lean` files
  that `#check_axioms` walks (the target `sourcePaths`, which the library
  `FirCheck` needs). Code that adds a read at elaboration, of a file, a
  directory, the environment or the clock, declares it in the same PR. The
  `firspec` executable reads the ADRs and `FIRSPEC_COMMIT` when it renders, not
  at elaboration, so it needs no input.

The human approved this performance ticket on 2026-11-09, in #275.

## Why

Each run built `lean/` twice and `docs/spec/` once, about 5 to 6 minutes
each, also when a PR touched neither, as 19 of 40 merged PRs did. Every merge
is still checked from scratch, and a PR cannot write an entry that `main` or
another PR reads.

## Rejected alternatives

- **No cache.** A hit skips checks, but only checks whose inputs `main`
  already checked.
- **Two entries, one per package.** `cross` would not download
  `docs/spec/`'s build, but each run would add two entries and `ci.yml` two
  steps.
- **Saving from pull requests.** Their entries would fill the 10 GB cache.
- **Tracing the file list for all of `FirTest`.** Adding a file would
  rebuild every test module, not one.
