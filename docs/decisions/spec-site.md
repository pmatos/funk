# Current decisions: the spec site

This page says what holds today for the spec, its published site and the Lean
build behind them. It summarizes the ADRs it cites. When this page and an ADR
disagree, that is a bug in this page (ADR-2026-11-09-1610).

## What the spec is

The spec is literate Lean, rendered with Verso, Lean's documentation tool
(ADR-2026-10-29-2015). The Lean definitions are the normative spec. The prose
makes them readable by a person. The spec keeps the Wasm spec's chapters:
abstract syntax, validation, execution and text format.

No change to fir's semantics merges without its spec section, formal and
readable. CI builds the document on every PR. The Rust verifier is hand-written
and tested against Lean. The differential harness catches drift between the
two: `funk verify` and the Lean validation rules must agree on every corpus
module.

`lean/` is the Lean package and holds every Lean definition of fir. It holds
the chapters as literate modules, the `.fir` parser and printer, and the
proofs. It also holds the `fir-ref` executable. The execution chapter's
definitions are the reference interpreter.

`docs/spec/` is the Verso document. It holds the entry point, the order of the
chapters and prose that belongs to no single definition. It also holds the
readable documents described below (ADR-2026-11-05-2012). It adds no definition
that the semantics depends on. The rendered document is a build output and is
not committed.

## The readable layer

The spec's default view follows the style of the WebAssembly specification
(ADR-2026-11-05-2012). The Lean stays normative. A section on the readable
layer shows its Lean module's module docs. In place of each declaration it
shows a readable block. A block is prose for a newcomer, with KaTeX math and
grammar boxes. Without JavaScript, a reader sees the LaTeX source of the math.

Under each block, an HTML `<details>` holds the Lean of the declarations the
block explains. That means their doc comments, statements and proofs,
highlighted with hovers. It also holds the code before them that defines
nothing, such as `variable` and `namespace`. It opens with one click and needs
no JavaScript. Every line of the module is on the page.

The readable blocks of the module `Fir.X.Y` are a Verso document. It is
`docs/spec/FirSpec/X/Y.lean`, the module `FirSpec.X.Y`. `FirSpec.lean` renders
the section with `{includeReadable "." Fir.X.Y "Title" FirSpec.X.Y (level := 2)}`.
The readable layer adds nothing to `lean/`.

### Moving sections to the readable layer

After the pilot of `Fir.Core.Ops` and `Fir.Execution.CallSteps`, the spec moves
chapter by chapter. The order is abstract syntax, validation, execution, then
text format (ADR-2026-11-05-2012). A chapter moves in one PR or, when it is
long, in several PRs. Each of those PRs covers a run of consecutive sections
(ADR-2026-11-05-2251). A section that has not moved keeps rendering with
`{includeLiterate}`, so the spec is whole between the PRs. A chapter may mix
readable and literate sections for a while.

A section whose Lean module declares nothing keeps `{includeLiterate}`
(ADR-2026-11-05-225128). `Fir.Execution.PoisonUB` is one such module. Its
module prose is still rewritten in the readable voice, in the PR that moves the
sections around it. It has no document in `docs/spec/FirSpec/`. If the module
gains a declaration, its section moves to `{includeReadable}` with a document.

## Checks that keep the prose true to the Lean

Drift between a readable block and its Lean is a build error
(ADR-2026-11-05-2012). The library `docs/spec/FirSpecSite/` checks these when
the document is elaborated:

- `:::readable` names the declarations a block explains, and each must exist.
- It pins a fingerprint of what they say. That is a theorem's statement, a
  definition's type and body, an inductive type's constructors, or a
  structure's fields and defaults.
- The fingerprint is a hash of Lean's terms, so a new proof keeps it.
- A definition that these only refer to counts by its name. A block whose prose
  restates such a definition, from any module, adds it with `(pin := P)`. The
  fingerprint then covers its body too.
- A `grammar T` box tags each alternative with the constructors it shows. The
  boxes of a block show every constructor of `T` exactly once. The block must
  name `T`.
- `{includeReadable}` fails unless the document explains every declaration of
  the module exactly once and names nothing else.
- `{includeReadable}` also fails on a document with no readable block
  (ADR-2026-11-05-225128). That catches a document that was never imported.

When the Lean changes, the build fails and prints the new signatures and the
new fingerprint. It asks for the block to be read again. The fingerprint is
updated in the same PR. A new declaration in a module on the readable layer
needs a readable block before the build passes. A toolchain bump can change
Lean's terms for unchanged sources, and the bump PR then updates the pins.

Module docs are pinned too (ADR-2026-11-09-1345). Each readable document holds
one `:::moduleDocs (fingerprint := "...")` directive when its Lean module has
`/-! -/` docs. The fingerprint covers every declaration that the document's
blocks explain, in any order. The build fails when the directive is missing or
stale, and names the new value. The pin covers the code, not the text of the
docs. A change to what a module says needs both the block's pin and the
module's pin. A change to a proof needs neither. An edit to module docs alone
needs no new pin. A module that declares nothing has no pin.

Every module under `lean/Fir` is in the spec. `firspec` fails when
`docs/spec/FirSpec.lean` has no `{includeReadable}` or `{includeLiterate}` line
for a module. These checks run in the `fir-spec` hook.

Some gaps are accepted (ADR-2026-11-09-1345):

- A stale fingerprint forces a look, not a correct rewrite. That stays with
  review, and the PR template has a checkbox for it. No check looks for a
  change in the prose.
- Pins stay explicit, with no transitive hashing. A block that restates a
  definition without pinning it goes unnoticed. Writing a block still includes
  pinning each definition its prose restates (ADR-2026-11-05-2012).
- A module doc can restate a definition from another module without any pin
  covering it. So can a module that declares nothing.

## Toolchain and packages

`lean/lean-toolchain` is the one pin (ADR-2026-10-29-2135). It names a stable
Lean release, now `leanprover/lean4:v4.35.0`. `docs/spec/lean-toolchain` is a
symlink to it. Nightlies and release candidates are not used.

`lean/` is the Lake package `fir`, with no dependencies. That means no Mathlib,
no Verso and no LeanMLIR. Adding a dependency takes a new ADR. Its
`lakefile.lean` sets `doc.verso` and turns off `doc.verso.suggestions`. It is a
Lean file because TOML cannot set both options. Its empty `lake-manifest.json`
is committed.

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
the same PR (ADR-2026-10-30-1837).

## The build script and its guards

`scripts/build-spec.sh [--update] [OUTPUT_DIR]` is the one build command
(ADR-2026-10-29-2135). It runs `lake build --wfail` in `lean/`
(ADR-2026-10-30-1837). Then it runs `lake build` and
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
  repository. Do not set it to the repository root.

Without the guards, Lake's git calls can rewrite this repository's `origin` and
move its `HEAD`. When Lake fails with "not a git repository", the guard has
stopped git at a broken clone. Delete that package's directory under
`.lake/packages` and rebuild. The script also unsets `GH_TOKEN` and
`GITHUB_TOKEN`, because lakefiles and elaboration can run arbitrary code.

The build needs `elan` on `PATH`, and the script adds `~/.elan/bin` when it is
not there. `scripts/ensure-hooks.sh` warns when elan is missing and says how to
install it. It does not fail. A commit that changes the Rust crates still needs
elan, because the `fir-round-trip` hook builds `lean/` (ADR-2026-10-30-1250).

The `fir-spec` hook runs the script when a file under `lean/` or `docs/spec/`
changes, or the script itself (ADR-2026-10-29-2135). It also runs when a file
in `docs/adrs/` changes (ADR-2026-10-30-1439). So committing an ADR renders the
spec, which takes several minutes in a fresh clone or worktree.

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

## What Lean code in lean/ may not do

The Lean build runs an axiom check over `lean/` (ADR-2026-10-30-1452).
`FirTest/Axioms.lean` defines the command `#check_axioms`. The root of `FirTest` imports every module of `lean/` and runs
`#check_axioms Fir FirRef FirTest` as its last command. The check names each
declaration of those libraries, or of the root, that does one of these:

- depends on an axiom other than `propext`, `Classical.choice`, `Quot.sound` or
  an axiom of native evaluation;
- is `unsafe`, or is an opaque constant with an `_unsafe_rec`, which is what
  `partial` makes;
- has an `implemented_by` or an `extern` attribute.

So `sorry`, every other axiom, `unsafe`, `partial`, `implemented_by` and
`@[extern]` are banned in `lean/` (ADR-2026-10-30-1838). Code that must be
`partial`, `unsafe` or `extern` cannot live in `lean/` without a new ADR
(ADR-2026-10-30-1452).

Native evaluation is allowed, because the human ruled to trust Lean's compiler
(ADR-2026-10-30-1838). This covers `native_decide`, `decide +native`, and
`bv_decide` when it uses native evaluation. An axiom counts as native evaluation
only when all of these hold:

- its name ends in `_native`, a tactic's name, and a part that starts with
  `ax_`;
- its type is `e = true` for a closed term `e : Bool`;
- the check compiles and runs `e` again with `Lean.Meta.nativeEqTrue` and gets
  `true`.

The trusted base therefore includes Lean's compiler and the runtime that
evaluates compiled code. A `@[csimp]` swap stays allowed, because each one is
proved. It must rest on the three standard axioms alone. The check rejects a
swap that depends on an axiom of native evaluation. A toolchain that changes how
native evaluation is recorded needs the check updated in the same PR.

The check also fails in these cases (ADR-2026-10-30-1452):

- A `.lean` file in `lean/` is not imported by the root.
- A `.lean` file's module is not under a root the check names.
- A root has no declaration, so a renamed library is not skipped in silence.
- Any text but white space follows the check.

`lakefile.lean` and hidden directories such as `.lake` are exempt from the file
checks.

So a new module of `lean/` is imported by the root of `FirTest`. A new library
is also named in its `#check_axioms`. A stray `.lean` file fails the build,
tracked or not. The check runs whenever Lake builds `FirTest`. That covers the
`fir-spec` hook and every script that calls `scripts/build-spec.sh --lean`. A
type that holds a list of itself writes its `Repr` instance by hand, since a
derived one is `partial`.

Any warning in `lean/` fails the build (ADR-2026-10-30-1837). The `fir-spec`,
`fir-ref-test`, `fir-round-trip` and `fir-harness` hooks build `lean/` through
the script, so each fails too. This catches a `sorry` inside an `example`, which
the axiom check cannot see. It also fails on warnings unrelated to soundness,
such as an unused variable or a deprecated name. Lean gives no warning for
native evaluation, and it is allowed in an `example` too. The build in
`docs/spec/` stays a plain `lake build`, because Verso's build can warn about
code we do not own.

A `by_cases` under `lean/` on a proposition with no `Decidable` instance needs
`classical` before it, in the same tactic block (ADR-2026-11-06-0224). In Lean v4.35.0, Verso's elaboration of module docs can
race with `open Classical`. A missing `classical` then fails at random, not on
every build. The `classical` lines look redundant. Do not remove them while the
toolchain lacks commit `541dbdcd`. A `by_cases` whose proposition has an
instance stays as it is.

## The ADR appendix and its citations

The spec's last part is the appendix "Architecture decision records", tagged
`adrs` (ADR-2026-10-30-1439). When `firspec` renders, it reads each ADR in
`docs/adrs/` in name order. It parses each with MD4Lean and adds one part per
ADR, after an index table of id, decision and status. Nothing is generated into
the tree, so the site matches the commit it names.

An ADR's page has the tag and short title `ADR-<id>`. Its address is
`adrs/ADR-<id>/`. Its title is `ADR-<id>: ` and the text of the file's level-1
heading. The next block must be the `Status:` line. Deeper headings become
unnumbered sections on the same page.

The build fails, naming the file, on Markdown the document cannot show as GitHub
does. That is raw HTML, images, horizontal rules, strikethrough, task lists and
hard line breaks. It also covers any entity other than `&amp;`, `&lt;`, `&gt;`,
`&quot;`, `&apos;`, `&nbsp;` or a numeric one.

A URL in an ADR stays as written. A relative path to another ADR links to its
page. Any other relative path links to the file on GitHub at `main`. The
build fails if the file does not exist.

`firspec` turns each citation in the document's text into a link to the ADR's
page. That covers `FirSpec.lean`, the docs that `{includeLiterate}` renders, and
the ADRs with their status lines. These rules apply:

- A citation in a heading, or in the text of a link to anything else, cannot
  link. `firspec` prints each one with its place and exits with status 1.
- A citation in a code span or fenced code block is quoted. It is not linked
  or checked.
- A citation of no ADR fails the build, with its file, line and column. A
  malformed id fails too. A citation matches a whole id, with four or six digits
  after the date.
- After rendering, `firspec` checks that every ADR has its page. It also checks
  that every citation in each page's prose is inside a link to that ADR.

The code is the Lean library `FirSpecSite` in `docs/spec/`, and its `#guard`
tests run when it builds.

The spec build reads only the spec's sources. The `adr-citations` hook checks
every citation in every tracked text file, on every commit
(ADR-2026-11-05-1709). Its grammar is a port of the spec checker's. The table
`docs/spec/FirSpecSite/citation-cases.json` holds cases that both checkers'
tests read, so a change to either grammar adds a case. Files whose bad citations
are test data on purpose are listed, with a reason, in `FIXTURES` in the script.

## Publishing the site

Every push to `main` deploys the document to GitHub Pages
(ADR-2026-10-30-1031). `.github/workflows/pages.yml` runs on each such push, and
by hand through `workflow_dispatch`. Both its jobs run only for
`refs/heads/main`. The `github-pages` environment accepts deployments only from
`main`. Pull requests never deploy; their CI builds the document through the
hook.

The `build` job runs `scripts/build-spec.sh OUT`, the script the hook runs. It
deploys `OUT/html-multi`. It uploads the site with
`actions/upload-pages-artifact`, and the `deploy` job publishes it with
`actions/deploy-pages`. No HTML is committed and no branch is written.

The `build` job may only read the repository, and it has no OIDC token. Only the
`deploy` job has `pages: write` and `id-token: write`, and it runs no code from
the repository.

The concurrency group `pages-<ref>` runs one run per ref and never cancels one
half way. A newer push replaces a run that is still waiting. So `main` deploys
its latest commit and may skip the ones between. A failed build skips the
deploy, so the previous site stays up.

The workflow restores the toolchain and `docs/spec/.lake/packages` from the
cache that `ci.yml` saves, with the same key. It never saves a cache. The Lean
setup steps exist in three copies: the `lean` and `cross` jobs and `pages.yml`
(ADR-2026-11-05-1408). The `pages.yml` copy has four steps and no save
(ADR-2026-11-05-1954). Comments say to change all three together. If the keys
drift, the deploy still works but builds Verso every time.

The site is <https://p.ocmatos.com/funk/>, under the custom domain of the
owner's user site. It is the repository's homepage, and `docs/spec/README.md`
links to it.

Every rendered page names the commit it was built from (ADR-2026-10-30-1046).
`scripts/build-spec.sh` reads the commit with `git rev-parse HEAD`. It adds
`-dirty` when `git status --porcelain` lists anything, untracked files included.
It passes the first 12 hex digits, plus any `-dirty`, in
`FIRSPEC_COMMIT`. In Actions it also passes the commit's GitHub page in
`FIRSPEC_COMMIT_URL`.

`docs/spec/FirSpecMain.lean` reads both when it renders. It adds "Built from
commit ..." to every page through `extraContents`, linked when there is a URL.
When `FIRSPEC_COMMIT` is unset, pages carry no line. A build in the hook of a
commit is `-dirty`, because that commit does not exist yet. A CI build is
`-dirty` when an earlier hook changed a file.
