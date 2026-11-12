# Current decisions: the Lean build

This page continues [spec-site.md](spec-site.md). It says how fir's Lean code
is pinned and built, and what Lean code in `lean/` may do. It is the record:
when this page and an ADR disagree, the page wins, and the ADR is fixed or
deleted (ADR-2026-11-09-1610).

## Toolchain and packages

`lean/lean-toolchain` is the one pin (ADR-2026-10-29-2135). It names a stable
Lean release, now `leanprover/lean4:v4.35.0`. `docs/spec/lean-toolchain` is a
symlink to it. Nightlies and release candidates are not used.

Rejected: a nightly toolchain. Verso and Mathlib tag stable releases, and
nightlies are hard to reproduce.

`lean/` is the Lake package `fir`, with no dependencies. That means no Mathlib,
no Verso and no LeanMLIR. Adding a dependency means editing
ADR-2026-10-29-2135 and this page first. Its `lakefile.lean` sets `doc.verso`
and turns off `doc.verso.suggestions`. It is a Lean file because TOML cannot
set both options. Its empty `lake-manifest.json` is committed.

Rejected: depending on Mathlib. Nothing in the spec needs it, and it adds
thousands of modules and a cache to keep working. Rejected too: chapters as
Verso documents with `lean` code blocks, which would make `fir`, and `fir-ref`
with it, depend on Verso.

The package has three default targets (ADR-2026-10-30-1250). The library `Fir`
is the spec. The library `FirRef` and the executable `fir-ref` hold what is not
the spec. The library `FirTest` holds the Lean tests. So `lake build` in `lean/`
builds the spec, `fir-ref` and the tests, and runs the tests. The document
renders `Fir` only.

`docs/spec/` is the Lake package `firspec` (ADR-2026-10-29-2135). It requires
`fir` by path and `verso` at the git tag named like the toolchain. Its
`lake-manifest.json` is committed. `FirSpec.lean` is the document. It holds the
chapter order, the prose that belongs to no definition and the include lines.
The `FirSpec` library needs an `input_dir` target over `lean/Fir`. So any change
to a source rebuilds the document, even one that leaves compiled code unchanged.

With `doc.verso`, Lean checks module and declaration docs at build time. A
`{name}` reference must name a constant that is already defined. So prose that
names a definition must come after it.

A toolchain bump is one PR. It changes `lean/lean-toolchain` and the `verso` rev
to the same new stable tag. It runs `scripts/build-spec.sh --update`. It commits
both files and the updated `docs/spec/lake-manifest.json`. Never run a bare
`lake update`. A bump that deprecates a name used in `lean/` fixes those uses in
the same PR (ADR-2026-10-30-1452).

## The build script and its guards

`scripts/build-spec.sh [--update] [OUTPUT_DIR]` is the one build command
(ADR-2026-10-29-2135). It runs `lake build --wfail` in `lean/`
(ADR-2026-10-30-1452). Then it runs `lake build` and
`lake exe firspec --output OUTPUT_DIR` in `docs/spec/`. The output defaults to
`docs/spec/_out`, which git ignores. `--update` runs `lake update` in
`docs/spec/` under the guards below, then builds as usual.

`scripts/build-spec.sh --lean` builds `lean/` alone, under the same guards
(ADR-2026-10-30-1250). `fir-ref` is then `lean/.lake/build/bin/fir-ref`. Every
script and hook that needs `fir-ref` calls this mode.

Every Lake run in `lean/` or `docs/spec/` goes through the script or applies
both of its guards (ADR-2026-10-29-2135):

- Unset each variable that `git rev-parse --local-env-vars` lists. Git hooks
  set variables such as `GIT_DIR`, and those override a package clone's own
  repository.
- Set `GIT_CEILING_DIRECTORIES` to `lean/.lake/packages` and
  `docs/spec/.lake/packages`. Git then cannot climb from a broken clone to this
  repository.

Rejected: setting `GIT_CEILING_DIRECTORIES` to the repository root. It would
also stop git from finding this repository from `docs/spec/`.

Without the guards, Lake's git calls can rewrite this repository's `origin` and
move its `HEAD`. When Lake fails with "not a git repository", the guard has
stopped git at a broken clone. Delete that package's directory under
`.lake/packages` and rebuild. The script also unsets `GH_TOKEN` and
`GITHUB_TOKEN`, because lakefiles and elaboration can run arbitrary code. The
LeanMLIR spike runs Lake outside both packages, and its report,
`docs/spikes/leanmlir.md`, says how to guard those runs.

The build needs `elan` on `PATH`, and the script adds `~/.elan/bin` when it is
not there. `scripts/ensure-hooks.sh` warns when elan is missing and says how to
install it. It does not fail. A commit that changes the Rust crates still needs
elan, because the `fir-round-trip` hook builds `lean/` (ADR-2026-10-30-1250).

The `fir-spec` hook runs the script when a file under `lean/` or `docs/spec/`
changes, or the script itself (ADR-2026-10-29-2135). It also runs when a file
in `docs/adrs/` changes, because the spec renders the ADRs
([the ADR appendix](spec-site.md#the-adr-appendix-and-its-citations)). So
committing an ADR renders the spec, which takes several minutes in a fresh
clone or worktree.

The `lean` job of `ci.yml` runs `fir-spec` (ADR-2026-11-05-1408). It installs
elan and the pinned toolchain, and it is the one job that saves the Verso
build. The `cross` job builds `lean/` again. CI caches the toolchain and
`docs/spec/.lake/packages`, keyed on the toolchain file and the document's
manifest (ADR-2026-10-29-2135). The cache is saved once Verso is built, even if
a later hook fails. A cancelled run does not save it. `docs/spec/.lake/build`
is never cached, so the document is always rebuilt from its sources.

The elan tarball is cached too (ADR-2026-11-05-1954). `scripts/ci-install.sh
elan` downloads it only on a cache miss. It checks the file against its SHA-256
on every run. The `lean` job saves that cache. `cross` and `pages.yml` only
restore it.

Rejected: `leanprover/lean-action`. A checksummed elan tarball needs no
third-party action.

## What Lean code in lean/ may not do

The Lean build runs an axiom check over `lean/` (ADR-2026-10-30-1452).
`FirTest/Axioms.lean` defines the command `#check_axioms`. The root of
`FirTest` imports every module of `lean/` and runs
`#check_axioms Fir FirRef FirTest` as its last command. The check names each
declaration of those libraries, or of the root, that does one of these:

- depends on an axiom other than `propext`, `Classical.choice`, `Quot.sound` or
  an axiom of native evaluation;
- is `unsafe`, or is an opaque constant with an `_unsafe_rec`, which is what
  `partial` makes;
- has an `implemented_by` or an `extern` attribute.

So `sorry`, every other axiom, `unsafe`, `partial`, `implemented_by` and
`@[extern]` are banned in `lean/` (ADR-2026-10-30-1452). Code that must be
`partial`, `unsafe` or `extern` stays out of `lean/` until ADR-2026-10-30-1452
and this page are edited to allow it.

Rejected: a text search for `sorry`, `partial` and the rest. It cannot see the
axioms a declaration uses through other declarations, nor code that a macro
writes, and prose may use the words. Rejected too: `#print axioms` for each
theorem, where a missing line passes in silence, and a separate executable or
hook that loads the built modules, a second Lake entry point to guard.

Native evaluation is allowed, because the human ruled on 2026-10-30, in #52, to
trust Lean's compiler (ADR-2026-10-30-1452). This covers `native_decide`,
`decide +native`, and `bv_decide` when it uses native evaluation. An axiom
counts as native evaluation only when all of these hold:

- its name ends in `_native`, a tactic's name, and a part that starts with
  `ax_`;
- its type is `e = true` for a closed term `e : Bool`;
- the check compiles and runs `e` again with `Lean.Meta.nativeEqTrue` and gets
  `true`.

Rejected: a text check that banned `native_decide`. It was proposed, then
dropped when the human chose to trust the compiler.

The trusted base therefore includes Lean's compiler and the runtime that
evaluates compiled code. A `@[csimp]` swap stays allowed, because each one is
proved. It must rest on the three standard axioms alone; the human accepted
this narrowing on 2026-11-02, in #52. The check rejects a swap that depends on
an axiom of native evaluation: the check runs a claim again with every swap
applied, so a swap proved from a native axiom could make that axiom's false
claim run as `true`. A toolchain that changes how native evaluation is
recorded needs the check updated in the same PR.

The check also fails in these cases (ADR-2026-10-30-1452):

- A `.lean` file in `lean/` is not imported by the root.
- A `.lean` file's module is not under a root the check names.
- A root has no declaration, so a renamed library is not skipped in silence.
- Any text but white space follows the check.

`lakefile.lean` and hidden directories such as `.lake` are exempt from the file
checks. `FirTest/Axioms.lean` imports Lean's own modules, such as
`Lean.Util.CollectAxioms`. They are part of the toolchain, not a dependency of
the package `fir`.

So a new module of `lean/` is imported by the root of `FirTest`. A new library
is also named in its `#check_axioms`. A stray `.lean` file fails the build,
tracked or not. The check runs whenever Lake builds `FirTest`. That covers the
`fir-spec` hook and every script that calls `scripts/build-spec.sh --lean`. A
type that holds a list of itself writes its `Repr` instance by hand, since a
derived one is `partial`.

Any warning in `lean/` fails the build (ADR-2026-10-30-1452). The human ruled
this on 2026-10-30, in #52. The `fir-spec`, `fir-ref-test`, `fir-round-trip`
and `fir-harness` hooks build `lean/` through the script, so each fails too.
This catches a `sorry` inside an `example`, which the axiom check cannot see.
It also fails on warnings unrelated to soundness, such as an unused variable
or a deprecated name. Lean gives no warning for native evaluation, and it is
allowed in an `example` too. The build in `docs/spec/` stays a plain
`lake build`, because Verso's build can warn about code we do not own.

Rejected: keeping warnings as warnings. A `sorry` inside an `example` would
pass.

### A `by_cases` without an instance runs under `classical`

A `by_cases` under `lean/` on a proposition with no `Decidable` instance needs
`classical` before it, in the same tactic block. `by_cases` turns on
`Classical.propDecidable` through `open Classical`, which uses a process-wide
list of scoped extensions. In Lean v4.35.0, Verso's elaboration of module docs
swaps that list for an empty one on the main thread while proofs elaborate on
other threads ([leanprover/lean4#15817](https://github.com/leanprover/lean4/issues/15817)).
A missing `classical` then fails at random, not on every build; it failed one
Pages build of `main` (#184). `classical` adds the instance as a local one,
without the list.

The `classical` lines look redundant. Do not remove them while the toolchain
lacks commit `541dbdcd`, the fix in
[leanprover/lean4#15839](https://github.com/leanprover/lean4/pull/15839). A
`by_cases` whose proposition has an instance, such as `x = y` on `Name`, stays
as it is.

Rejected: `rcases Classical.em p with h | h`. It is safe too, but it names the
goals `inl` and `inr`, and two proofs select the goal `neg`. Rejected too:
turning `doc.verso` off, since the spec renders our docstrings as Verso.
