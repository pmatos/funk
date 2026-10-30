# The spec renders every ADR in an appendix and links every ADR citation to it

Status: accepted

## Context

The spec cites ADRs by id, such as ADR-2026-10-29-2015, in plain text, and
the published site (ADR-2026-10-30-1031) did not hold the ADRs, so a reader
had to go to GitHub to follow a citation. On 2026-10-30 the human asked for
every citation to be a link, and for the ADRs to be published, pretty
printed, as an appendix of the site
([#46](https://github.com/pmatos/funk/issues/46)). Nothing checked that a
citation names an ADR that exists
([#44](https://github.com/pmatos/funk/issues/44)).

Facts about Verso `v4.35.0`, the pinned version (ADR-2026-10-29-2135):

- `lake exe firspec` gets the whole document as a `Part Manual` value from
  `%doc FirSpec` and passes it to `manualMain`, which traverses and renders
  it. A part added to that value first is rendered like any other, with the
  same style, navigation and search.
- A part's `tag` is a cross-reference target. `Inline.ref`, the inline
  behind Verso's `{ref}` role, links to a tag, and Verso computes the address
  on each page. A tag that resolves to nothing is a render error.
- `{includeLiterate}` turns the module and declaration docs of `lean/` into
  ordinary Verso text, so a citation in a docstring is a text inline of that
  value.
- MD4Lean, which Verso requires for Markdown docstrings, parses Markdown,
  GitHub's tables included. It is already in `docs/spec/lake-manifest.json`.
  Verso's own Markdown converter rejects tables.

## Decision

- **The appendix is a part of the same document.** `FirSpec.lean` ends with
  the part "Architecture decision records", tagged `adrs`, and its prose.
  When `firspec` renders, it reads every file in `docs/adrs/` but
  `README.md`, in name order, parses each with MD4Lean, and adds one part
  per ADR to the appendix, after an index table of id, decision and status.
  Nothing is generated into the tree or committed: the files are read on
  every render, so the site matches the commit it names.
- **An ADR's page.** Its tag, file name and short title are `ADR-<id>`, so
  its address is `adrs/ADR-<id>/`. Its title is `ADR-<id>: ` and the text of
  the level-1 heading that starts the file. The next block must be the
  `Status:` line, and the index shows what follows `Status:`. Deeper headings
  become unnumbered sections on the same page. Lists, code, tables, emphasis
  and links render as GitHub shows the file, where a bare `#5` is text, not
  a link. Markdown the document cannot show as GitHub does (raw HTML,
  images, horizontal rules, strikethrough, task lists, hard line breaks, an
  entity other than `&amp;`, `&lt;`, `&gt;`, `&quot;`, `&apos;`, `&nbsp;`
  or a numeric one) fails the build with the file's name.
- **Links in an ADR.** A URL stays as written. A relative path to another
  ADR links to its page. Any other relative path links to the file on
  GitHub at `main`, and the build fails if the file does not exist.
- **Every citation links.** Once the appendix is in, `firspec` replaces each
  citation in the document's text with an `Inline.ref` to `ADR-<id>`: in
  `FirSpec.lean`, in the docs that `{includeLiterate}` renders, and in the
  ADRs, their status lines and the index included. Code is left as it is.
- **A citation that cannot link fails the build.** The table of contents
  shows each heading inside a link, and a link cannot hold another. So a
  citation in a heading, or in the text of a link to anything but that ADR,
  cannot become a link to it. `firspec` prints each one with its place, the
  ADR's file for a citation in an ADR, and exits with status 1 before it
  renders.
- **Code is quoted, not cited.** A citation in a code span or a fenced code
  block, such as an example id, is neither linked nor checked. Lean code that
  the document shows as code keeps its comments as they are.
- **A citation of no ADR fails the build, located.** Before rendering,
  `firspec` reads the Lean files of `lean/`, the files at the top of
  `docs/spec/` and the ADRs, and prints
  `FILE:LINE:COL: ADR-<id> names no ADR in docs/adrs/` for each citation
  outside code whose id no ADR has, or a similar line for a malformed id.
  A citation matches a whole id: it ends at its last digit, and has four or
  six digits after the date. `firspec`, and so `scripts/build-spec.sh`, then
  exits with status 1.
- **The rendered pages are checked.** After rendering, `firspec` checks that
  every ADR has its page, and that every citation in the prose of every page
  (text in `<main>`, outside code, headings, navigation, scripts and styles)
  is inside a link to `adrs/ADR-<id>/#ADR-<id>`.
- **Where it lives.** The code is the Lean library `FirSpecSite` in
  `docs/spec/`, built with the document by `scripts/build-spec.sh`; its
  `#guard` tests run when it builds. The `fir-spec` hook also runs when a
  file in `docs/adrs/` changes. No new dependency.

## Alternatives

- **Generate Verso files from the ADRs before `lake build`.** It needs a
  conversion step in `build-spec.sh`, a place for the output outside git,
  and a way for Lake to notice a changed ADR. Reading the files when
  rendering needs none of them.
- **Elaborate the ADRs in `FirSpec.lean`** with Verso's
  `addPartFromMarkdown`. Lake would need `docs/adrs/` as an input to rebuild,
  and the converter rejects tables.
- **A separate HTML appendix** from MD4Lean's HTML renderer. It would not
  share the document's navigation, search or cross-references.
- **Write each citation as a `{ref}` link in the sources.** Every citation in
  `lean/` and the ADRs would change, and the ADRs would no longer read as
  plain Markdown on GitHub.
- **Check citations with a Python script in `build-spec.sh`.** The check and
  the linking would hold two definitions of a citation, which could
  disagree.

## Consequences

- A reader follows every citation without leaving the site, and the site's
  search finds the ADRs.
- A typo in a citation, or an ADR renamed under its citations, fails every
  build of the spec, with the file and line.
- Committing an ADR runs the `fir-spec` hook, which renders the spec. That
  takes seconds with a warm build, but several minutes in a fresh clone or
  worktree, which first builds Verso.
- An ADR must start with its title and its `Status:` line, as the template
  in `docs/adrs/README.md` does, use only the Markdown above, and cite ADRs
  in its text, not in a heading or in a link's text.
- Links to repository files point at `main`, so an old page links to the
  file as it is now.
- This covers #44 for the spec and the ADRs only. Citations in other files,
  such as `AGENTS.md`, the roadmap or Rust code, are not checked.
