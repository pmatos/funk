# The fir specification

The rendered spec is published at <https://p.ocmatos.com/funk/>. It is
rebuilt and deployed from every push to `main`, and each page names the
commit it was built from (ADR-2026-10-30-1031, ADR-2026-10-30-1046).

fir's specification is literate Lean, rendered with Verso
(ADR-2026-10-29-2015). Its chapters are the Lean modules of the package `fir`
in [`lean/`](../../lean), where each definition sits beside its prose. This
directory is the Verso document that renders them:
[`FirSpec.lean`](FirSpec.lean) gives the order of the chapters and the prose
that belongs to no definition.

## The readable layer

Some sections show readable blocks, prose for a newcomer with notation in
the WebAssembly specification's style, in place of each declaration, and
hide the Lean under each one in a `<details>` (ADR-2026-11-05-2012). The
blocks of the module `Fir.X.Y` are the Verso document
`FirSpec/X/Y.lean`, which [`FirSpec/ReadableDocs.lean`](FirSpec/ReadableDocs.lean)
imports, and `FirSpec.lean` renders the section with
`{includeReadable "." Fir.X.Y "Title" FirSpec.X.Y (level := 2)}`.

A readable block names the declarations it explains, pins with
`(pin := …)` each further definition its prose restates, such as
`Fir.HasPath` here, and pins their fingerprint:

```
:::readable Fir.HasPath.bind (pin := Fir.HasPath) (fingerprint := "12286075038897393730")
*Theorem: a sequence has a path when its parts have one.* ...
:::
```

The build fails when a declaration's statement, body or constructors
change, or a pinned definition's body, printing the new signatures and
fingerprint: read the block again against the Lean, correct it, then pin
the new fingerprint. It also fails
when a declaration of the module has no block, and when a ```` ```grammar ````
box misses a constructor or shows one twice. To move a section, write its
document, import it in `FirSpec/ReadableDocs.lean`, pin each block with the
fingerprint the first build prints, and switch its `{includeLiterate}` to
`{includeReadable}`.

The `/-! -/` docs of a module render on its page, so each document also
pins them with one `:::moduleDocs (fingerprint := "…")` directive, closed by
`:::` on the next line. That fingerprint covers every declaration of the
module, so a change to what the module declares fails this pin too. Read
the module's docs again in `lean/Fir/`, correct them, then set the
fingerprint that the build prints (ADR-2026-11-09-1345).

The build also fails when a module under `lean/Fir` has no section in
`FirSpec.lean`, or in a chapter that it includes as a document of its own.
A chapter that would push `FirSpec.lean` over the file-size budget moves to
`FirSpec/Chapters/`, as the chapter on execution has: a `#doc` whose title
is the chapter's, which `FirSpec.lean` imports and includes with
`{include 1 FirSpec.Chapters.Name}`. Its sections are at `(level := 1)`, one
level below its own title.

## Appendix and build

The document ends with an appendix that renders every ADR in
[`docs/adrs/`](../adrs), and every ADR citation in the spec and the ADRs,
such as ADR-2026-10-29-2015, links to the ADR's page. The library in
[`FirSpecSite/`](FirSpecSite) adds both when `firspec` renders the
document, and the build fails, naming the file and line, on a citation of
an ADR that does not exist (ADR-2026-10-30-1439).

Build the Lean code and render the document with:

```sh
scripts/build-spec.sh            # writes docs/spec/_out/html-multi/index.html
scripts/build-spec.sh --update   # for a toolchain bump: lake update, then build
scripts/build-spec.sh --lean     # only lean/: the spec's definitions, fir-ref and the Lean tests
```

The last builds `lean/.lake/build/bin/fir-ref`, the reference interpreter's
executable, and runs the Lean tests in `lean/FirTest/`
(ADR-2026-10-30-1250).

The toolchain, the dependencies and the build are recorded in
ADR-2026-10-29-2135. The rendered document is a build output and is not
committed.
