# Current decisions: the spec site

This page says what holds today for the spec and its published site.
[spec-site-lean-build.md](spec-site-lean-build.md) continues it with the Lean
toolchain, the build script and what Lean code in `lean/` may do. It is the
record: when this page and an ADR disagree, the page wins, and the ADR is
fixed or deleted (ADR-2026-11-09-1610).

## What the spec is

The spec is Lean rendered with Verso, Lean's documentation tool
(ADR-2026-11-05-2012). The Lean definitions are the normative spec. The prose
makes them readable by a person. The spec keeps the Wasm spec's chapters:
abstract syntax, validation, execution and text format. The human chose this
on 2026-10-29 (P1 on #5). On 2026-11-05 the human said, on #161, that
"literate" meant a spec written clearly and backed by the Lean, not the Lean
shown verbatim.

Rejected: a spec DSL in the style of Wasm's SpecTec, which would generate the
Lean, the Rust verifier and the document. It is a larger tool than the spec
needs, and it stays open if the hand-written verifier starts to drift.

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
readable documents described below. It adds no definition that the semantics
depends on. The rendered document is a build output and is not committed.

Rejected: everything under `docs/spec/`, or everything under `lean/`. The
first moves fir's Lean definitions, the interpreter included, out of `lean/`.
The second leaves `docs/spec/`, where readers look for the spec, without the
document.

## The readable layer

The spec's default view follows the style of the WebAssembly specification
(ADR-2026-11-05-2012). The human asked for it on 2026-11-05 (#161) and approved
the pilot the same day. The Lean stays normative. A section on the readable
layer shows its Lean module's module docs. In place of each declaration it
shows a readable block. A block is prose for a newcomer, with KaTeX math and
grammar boxes. Without JavaScript, a reader sees the LaTeX source of the math.

Under each block, an HTML `<details>` holds the Lean of the declarations the
block explains. That means their doc comments, statements and proofs,
highlighted with hovers. It also holds the code before them that defines
nothing, such as `variable` and `namespace`. It opens with one click and needs
no JavaScript. Every line of the module is on the page.

Rejected: hiding the Lean without readable blocks, since doc comments alone
read like Lean. Rejected too: readable prose in `lean/`'s doc comments. `lean/`
has no Verso dependency, so its doc comments cannot hold the checked
directives, and every prose change would run the Lean test hooks.

The readable blocks of the module `Fir.X.Y` are a Verso document. It is
`docs/spec/FirSpec/X/Y.lean`, the module `FirSpec.X.Y`. `FirSpec.lean` renders
the section with `{includeReadable "." Fir.X.Y "Title" FirSpec.X.Y (level := 2)}`.
The readable layer adds nothing to `lean/`.

### Moving sections to the readable layer

After the pilot of `Fir.Core.Ops` and `Fir.Execution.CallSteps`, the spec moves
chapter by chapter. The order is abstract syntax, validation, execution, then
text format (ADR-2026-11-05-2012). A chapter moves in one PR or, when it is
long, in several PRs. Each of those PRs covers a run of consecutive sections.
A section that has not moved keeps rendering with `{includeLiterate}`, so the
spec is whole between the PRs. A chapter may mix readable and literate
sections for a while. Batches can be written at once. They all edit
`FirSpec.lean`, so a batch that lands later merges `main` and keeps both sides.

Rejected: one PR for a chapter of 40 or 55 sections. Review is what keeps the
prose true to the Lean, and no review reads that many against the Lean with
care.

A section whose Lean module declares nothing keeps `{includeLiterate}`.
`Fir.Execution.PoisonUB` is one such module. With no declaration there is no
Lean to hide and no block to write. Its module prose is still rewritten in the
readable voice, in the PR that moves the sections around it. It has no
document in `docs/spec/FirSpec/`. If the module gains a declaration, its
section moves to `{includeReadable}` with a document.

Rejected: dropping `{includeReadable}`'s check that a document has a readable
block, so that such a module could have one. The check catches a document that
was never imported.

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
- `{includeReadable}` also fails on a document with no readable block. That
  catches a document that was never imported.

When the Lean changes, the build fails and prints the new signatures and the
new fingerprint. It asks for the block to be read again. The fingerprint is
updated in the same PR. A new declaration in a module on the readable layer
needs a readable block before the build passes. A toolchain bump can change
Lean's terms for unchanged sources, and the bump PR then updates the pins.

Pins stay explicit: the human ruled on 2026-11-05 (#161). Rejected: hashing
every definition a block reaches, which would force re-pinning after almost
any change to the interpreter. Rejected too: pinning a theorem's
pretty-printed statement, which misses changes to definition bodies and
constructors and moves with the printer.

### Module docs and every module

The human ruled on each of #195's four gaps on 2026-11-09. Gaps 3 and 4 got a
check; gap 1 stays with review; gap 2 is accepted.

Module docs are pinned. Each readable document holds one
`:::moduleDocs (fingerprint := "...")` directive when its Lean module has
`/-! -/` docs. The fingerprint covers every declaration that the document's
blocks explain, in any order. The build fails when the directive is missing or
stale, and names the new value. The pin covers the code, not the text of the
docs. A change to what a module says needs both the block's pin and the
module's pin. A change to a proof needs neither. An edit to module docs alone
needs no new pin. A module that declares nothing has no pin.

Every module under `lean/Fir` is in the spec. `firspec` fails when
`docs/spec/FirSpec.lean` has no `{includeReadable}` or `{includeLiterate}` line
for a module. These checks run in the `fir-spec` hook.

Some gaps are accepted:

- A stale fingerprint forces a look, not a correct rewrite. That stays with
  review, and the PR template has a checkbox for it. No check looks for a
  change in the prose.
- Pins stay explicit, with no transitive hashing. A block that restates a
  definition without pinning it goes unnoticed. Writing a block still includes
  pinning each definition its prose restates (ADR-2026-11-05-2012).
- A module doc can restate a definition from another module without any pin
  covering it. So can a module that declares nothing.

Rejected: a check that a block's prose changed when its fingerprint did. It
would invite token edits.

## The ADR appendix and its citations

The spec's last part is the appendix "Architecture decision records", tagged
`adrs`. The human asked on 2026-10-30 (#46) for the ADRs to be published there
and for every citation to link to them. When `firspec` renders, it reads each
ADR in `docs/adrs/` in name order, every `.md` file but `README.md` and
`INDEX.md`. It parses each with MD4Lean and adds one
part per ADR, after an index table of id, decision and status. Nothing is
generated into the tree, so the site matches the commit it names. The
`fir-spec` hook runs when a file in `docs/adrs/` changes.

Rejected: generating Verso files from the ADRs before `lake build`. It needs a
conversion step, a place for the output outside git, and a way for Lake to
notice a changed ADR. Rejected too: Verso's `addPartFromMarkdown`, whose
converter rejects tables; a separate HTML appendix, which would not share the
document's navigation, search or cross-references; and writing each citation
as a `{ref}` link in the sources, after which the ADRs would no longer read as
plain Markdown on GitHub.

An ADR's page has the tag and short title `ADR-<id>`. Its address is
`adrs/ADR-<id>/`. Its title is `ADR-<id>: ` and the text of the file's level-1
heading. The next block must be the `Status:` line, and the index table shows
what follows `Status:`. Deeper headings become unnumbered sections on the same
page. Lists, code, tables, emphasis and links render as GitHub shows the file,
where a bare `#5` is text, not a link.

The build fails, naming the file, on Markdown the document cannot show as GitHub
does. That is raw HTML, images, horizontal rules, strikethrough, task lists and
hard line breaks. It also covers any entity other than `&amp;`, `&lt;`, `&gt;`,
`&quot;`, `&apos;`, `&nbsp;` or a numeric one.

A URL in an ADR stays as written. A relative path to another ADR links to its
page. Any other relative path links to the file on GitHub at `main`, so an old
page links to the file as it is now. The build fails if the file does not
exist.

`firspec` turns each citation in the document's text into a link to the ADR's
page. That covers `FirSpec.lean`, the docs that `{includeLiterate}` renders, and
the ADRs with their status lines. These rules apply:

- A citation in a heading, or in the text of a link to anything else, cannot
  link. `firspec` prints each one with its place and exits with status 1.
- A citation in a code span or fenced code block is quoted. It is not linked
  or checked. Lean code that the document shows as code keeps its comments as
  they are.
- A citation of no ADR fails the build, with its file, line and column. Before
  rendering, `firspec` reads for this the Lean files of `lean/`, the files at
  the top of `docs/spec/` and the ADRs. A malformed id fails too. A citation matches a whole id, with four or six digits
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

Rejected: a Python checker in `build-spec.sh` in place of `firspec`'s own.
The check and the linking would hold two definitions of a citation, which
could disagree. The hook's port for the other files keeps the two equal through
the shared table of cases.

## Publishing the site

Every push to `main` deploys the document to GitHub Pages. The human asked for
this on 2026-10-29 (#28). `.github/workflows/pages.yml` runs on each such push,
and by hand through `workflow_dispatch`. Both its jobs run only for
`refs/heads/main`. The `github-pages` environment accepts deployments only from
`main`. Pull requests never deploy; their CI builds the document through the
hook.

The `build` job runs `scripts/build-spec.sh OUT`, the script the hook runs. It
deploys `OUT/html-multi`. It uploads the site with
`actions/upload-pages-artifact`, and the `deploy` job publishes it with
`actions/deploy-pages`. No HTML is committed and no branch is written.

Rejected: committing the HTML to a `gh-pages` branch. Build output stays out of
git, and pushing a branch needs `contents: write` in the job that runs Lake.

The `build` job may only read the repository, and it has no OIDC token. Only the
`deploy` job has `pages: write` and `id-token: write`, and it runs no code from
the repository.

Rejected: deploying from a job of `ci.yml`, which holds a token for zizmor's
online audits. Rejected too: deploying on `workflow_run`, a privileged trigger
that zizmor flags.

The `deploy` job tries `actions/deploy-pages` up to three times, five minutes
each, each attempt only if the one before failed. GitHub's side sometimes never
finishes syncing a good artifact. The human asked for the retries on 2026-11-10
(PR #273).

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

Rejected: a composite action in `.github/actions/` for the shared steps.
zizmor's `self-repository` audit asks for a form that actionlint rejects, and
its `github-env` audit flags the `GITHUB_PATH` write inside the action.

The site is <https://p.ocmatos.com/funk/>, under the custom domain of the
owner's user site. It is the repository's homepage, and `docs/spec/README.md`
links to it. If that domain changes, the homepage and the README link change
with it.

### Every page names its commit

Every rendered page names the commit it was built from.
`scripts/build-spec.sh` reads the commit with `git rev-parse HEAD`. It adds
`-dirty` when `git status --porcelain` lists anything, untracked files included.
It runs git with `--no-optional-locks`, because a hook runs while git holds the
index. It passes the first 12 hex digits, plus any `-dirty`, in
`FIRSPEC_COMMIT`. In Actions it also passes the commit's GitHub page in
`FIRSPEC_COMMIT_URL`.

`docs/spec/FirSpecMain.lean` reads both when it renders. It adds "Built from
commit ..." to every page through `extraContents`, linked when there is a URL.
When `FIRSPEC_COMMIT` is unset, pages carry no line. A build in the hook of a
commit is `-dirty`, because that commit does not exist yet. A CI build is
`-dirty` when an earlier hook changed a file.

Rejected: reading the commit while Lean elaborates the document, since a warm
local build would show the commit of the last full build. Rejected too: editing
the rendered HTML, which depends on Verso's markup, and passing `GITHUB_SHA`,
a second source of the commit that would skip the `-dirty` check in CI.
