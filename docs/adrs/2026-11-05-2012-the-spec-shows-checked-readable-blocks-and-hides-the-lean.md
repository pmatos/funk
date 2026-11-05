# The spec shows readable blocks checked against the Lean, and hides the Lean under them

Status: accepted

## Context

ADR-2026-10-29-2015 makes the spec literate Lean: Verso's `{includeLiterate}`
renders each module of `lean/Fir` whole, so a reader meets every
definition, theorem statement and proof script verbatim. On 2026-11-05 the
human found the result hard to read for a newcomer and asked for the
WebAssembly specification's style
([#161](https://github.com/pmatos/funk/issues/161)): prose a newcomer can
follow and simplified definitions in mathematical notation by default, with
the Lean one click away. The Lean stays normative, and the readable layer
must not drift from it.

## Decision

- **Default view.** A section on the readable layer shows its Lean
  module's own prose, the module docs, as before. In place of each
  declaration it shows a readable block: prose for a newcomer, with
  notation as KaTeX math and grammar boxes in the WebAssembly style.
- **Hidden.** Under each readable block, an HTML `<details>` holds the Lean
  of the declarations the block explains: doc comments, statements and
  proofs, highlighted with their hovers as before, and the code before
  them that defines nothing, such as `variable` and `namespace`. It opens
  with one click and needs no JavaScript. Every line of the module is on
  the page.
- **Where it lives.** The readable blocks of the module `Fir.X.Y` are a
  Verso document `docs/spec/FirSpec/X/Y.lean`, the module `FirSpec.X.Y`.
  `FirSpec.lean` renders the section with
  `{includeReadable "." Fir.X.Y "Title" FirSpec.X.Y (level := 2)}` instead
  of `{includeLiterate}`. Nothing changes in `lean/`.
- **Drift is a build error.** The library
  [`docs/spec/FirSpecSite/`](../spec/FirSpecSite) checks, when the
  document is elaborated:
  - `:::readable N₁ … Nₖ (fingerprint := "…")` names the declarations it
    explains, each of which must exist, and pins a fingerprint of what they
    say: a theorem's statement, a definition's type and body, an inductive
    type's constructors and a structure's fields and defaults. It is a hash
    of Lean's terms, so a new proof keeps it. When the Lean changes, the
    build fails, prints the declarations' new signatures and the new
    fingerprint, and asks for the block to be read again.
  - A ```` ```grammar T ```` box in a readable block tags each alternative
    with the constructors it shows. The boxes of a block must show every
    constructor of `T` exactly once, and the block must name `T`.
  - `{includeReadable}` fails unless the document explains every
    declaration of the module exactly once, and names nothing else.
- **Rollout.** The pilot moves the core ops section (`Fir.Core.Ops`) and
  the section on a call step (`Fir.Execution.CallSteps`). Once the human
  accepts it, the rest of the spec moves one chapter per PR: abstract
  syntax, validation, execution, then text format. Until its PR, a section
  keeps rendering with `{includeLiterate}` as before.

## Alternatives

- **Hide the Lean only, without readable blocks.** The doc comments alone
  are written beside the code and read like Lean: the human asked for
  simplified definitions and plain statements.
- **Readable prose in `lean/` doc comments.** `lean/` has no dependency on
  Verso (ADR-2026-10-29-2135), so its doc comments cannot hold the checked
  directives, and every prose change would run the Lean test hooks.
- **Generate the notation from the Lean**, in the manner of the
  WebAssembly specification's SpecTec. It reads worse than written
  notation for proofs and definitions, and is a larger tool than the drift
  check needs; ADR-2026-10-29-2015 already keeps it open for later.
- **Pin a theorem's pretty-printed statement.** Easy to read in a diff, but
  it misses changes to definition bodies and constructors, and changes
  with the pretty printer.

## Consequences

- A change to what a declaration says fails the spec build until its
  readable block is read again and its fingerprint updated in the same
  PR. Updating the pin without reading the block is possible, but it is a
  visible line of the diff next to the prose.
- A new declaration in a module on the readable layer needs a readable
  block before the build passes.
- A toolchain bump can change Lean's terms for unchanged sources, and so
  fingerprints; the bump PR then updates the pins.
- Math renders with KaTeX, which needs JavaScript; without it, a reader
  sees the LaTeX source.
