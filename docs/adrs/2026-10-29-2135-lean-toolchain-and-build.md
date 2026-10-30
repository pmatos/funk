# fir's Lean code is pinned to a stable Lean release, has no dependencies, and is built by one script

Status: accepted

## Context

P1 (ADR-2026-10-29-2015) puts the spec's chapters in `lean/` as literate Lean
modules and the Verso document in `docs/spec/`. It leaves to
[#8](https://github.com/pmatos/funk/issues/8) how Lake and Verso are wired
together and how the Lean toolchain is pinned. ADR-2026-10-29-2030 leaves to
the same ADR whether `lean/` depends on Mathlib.

Facts, checked on 2026-10-29:

- fir's Lean semantics does not depend on LeanMLIR (ADR-2026-10-29-2030). The
  spike's own calculus built on Lean `v4.35.0` with no dependencies, and its
  proofs used only core Lean. `BitVec`, `bv_decide`, `omega`, `simp` and
  `grind` are part of Lean.
- Lean, Verso and Mathlib each tag every stable Lean release with the same
  name. All three have `v4.35.0`.
- Verso `v4.35.0` builds on Lean `v4.35.0`: 476 Lake jobs, about two minutes
  on 8 cores of a developer machine (a rough figure, not a measurement).
- Verso's `{includeLiterate}` renders a plain Lean module of another package
  as a part of a document: module docs become prose and sections,
  declaration docs and code are shown together, and `{name}` references are
  links. It runs `elan run <toolchain> lake query +Module:literate` in the
  document's directory, so that directory needs a `lean-toolchain` file.
- Lean's `doc.verso` option makes module and declaration docs Verso markup.
  Lean checks them at build time: a `{name}` reference must name a constant
  that is already defined.

## Decision

- **One pin.** `lean/lean-toolchain` pins a stable Lean release, now
  `leanprover/lean4:v4.35.0`. `docs/spec/lean-toolchain` is a symlink to it.
  No nightlies and no release candidates.
- **`lean/` is the Lake package `fir`, with no dependencies.** No Mathlib, no
  Verso, no LeanMLIR. Its `lakefile.lean` sets `doc.verso` and turns off
  `doc.verso.suggestions`. It is a Lean file because TOML cannot set both
  options: one name extends the other. Its empty `lake-manifest.json` is
  committed. Adding a dependency takes a new ADR.
- **`docs/spec/` is the Lake package `firspec`.** It requires `fir` by path
  and `verso` at the git tag named like the toolchain (`v4.35.0`). Its
  `FirSpec.lean` is the document: the order of the chapters, the prose that
  belongs to no definition, and one `{includeLiterate}` per module of `fir`.
  Its `lake-manifest.json` is committed.
- **A toolchain bump is one PR.** It changes `lean/lean-toolchain` and the
  `verso` rev to the same new stable tag, runs `lake update` in `docs/spec/`,
  and commits both files.
- **One build command.** `scripts/build-spec.sh [OUTPUT_DIR]` runs
  `lake build` in `lean/`, which also runs the `#guard` checks, then
  `lake build` and `lake exe firspec --output OUTPUT_DIR` in `docs/spec/`.
  The output defaults to `docs/spec/_out`, which is ignored by git. The
  `fir-spec` pre-commit hook runs the script when a file under `lean/` or
  `docs/spec/`, or the script itself, changes. A deployment of the document
  ([#28](https://github.com/pmatos/funk/issues/28)) uses the same script.
- **CI.** The `pre-commit` job installs elan `v4.2.4` from its release
  tarball, checked against its SHA-256, then the pinned toolchain. It caches
  the toolchain and `docs/spec/.lake/packages`, keyed on the toolchain file
  and the document's manifest. It saves the cache once Verso is built, even
  if a later hook fails.
- **Hooks that run Lake keep its git calls inside the package clones.** Lake
  runs git inside each package clone under `.lake/packages`. Two paths let
  those calls act on this repository instead; in tests they rewrote
  `origin`, fetched Verso's tags, and moved `HEAD` with `checkout --detach`
  and `clean -xf`.
  - Git runs hooks with `GIT_DIR`, `GIT_INDEX_FILE` and similar variables
    set, and those override the clone's own repository. Guard: unset each
    variable that `git rev-parse --local-env-vars` lists.
  - Lake treats a package as cloned when its `.git` exists. If that `.git`
    is broken (an interrupted clone, a full disk), git skips it and climbs
    to this repository, even with no variable set. Guard: set
    `GIT_CEILING_DIRECTORIES` to `lean/.lake/packages` and
    `docs/spec/.lake/packages`, so git stops there. Not the repository root,
    which would also stop git from finding this repository from `docs/spec/`.

  Every hook that runs Lake goes through `scripts/build-spec.sh`, or applies
  both guards as the script does. The script also unsets `GH_TOKEN` and
  `GITHUB_TOKEN`, because lakefiles and elaboration can run arbitrary code.
- [#10](https://github.com/pmatos/funk/issues/10) extends this build with the
  Lean tests and the `fir-ref` executable.

## Alternatives

- **Depend on Mathlib.** Nothing in the spec needs it yet. It would add
  thousands of modules to build or download, and a cache to keep working.
  Because Mathlib tags each stable release, a later ADR can add it at the
  same pin if a proof (#11, #14) needs it.
- **Chapters as Verso documents with `lean` code blocks**, as in the spike's
  page. The definitions would live inside Verso documents, so `fir`, and
  `fir-ref` with it, would depend on Verso.
- **A nightly toolchain.** Verso and Mathlib tag stable releases, and
  nightlies are hard to reproduce, as LeanMLIR's frozen nightly shows.
- **`leanprover/lean-action`.** It installs elan and caches one package
  directory. A checksummed elan tarball needs no third-party action.

## Consequences

- One file pins the toolchain, and committed manifests pin every dependency
  of the document, so builds are reproducible.
- The first build in a fresh clone, or in CI with a cold cache, builds Verso.
- Prose that names a definition with `{name}` must come after it.
- The document build needs `elan` on `PATH`. The script adds `~/.elan/bin`
  when it is not.
