# The spec is Lean rendered with Verso, shown as readable blocks checked against the Lean

Status: accepted
Tier: direction; area: spec-site

## Decision

- The spec keeps the WebAssembly spec's chapters: abstract syntax, validation,
  execution and text format. Its Lean definitions in `lean/` are normative,
  and the execution chapter's definitions are the reference interpreter.
  Verso renders the document from `docs/spec/`, which adds no definition that
  the semantics depends on. The rendered document is not committed.
- No change to fir's semantics merges without its spec section, formal and
  readable. The Rust verifier is hand-written and tested against the Lean.
- The default view is readable, in the WebAssembly spec's style. In place of
  each declaration it shows a readable block: prose for a capable newcomer,
  with KaTeX math and grammar boxes. The Lean of those declarations, with
  their statements and proofs, sits under the block in a `<details>`, one
  click away. Every line of a module is on the page.
- Drift between a block and its Lean fails the build. A block names the
  declarations it explains and pins a fingerprint of their terms, and of
  each definition its prose restates. Pins are explicit, with no transitive
  hashing. A document explains every declaration of its module exactly
  once.

The human chose literate Lean rendered with Verso on 2026-10-29 (P1 on #5).
On 2026-11-05, on #161, the human said that "literate" meant a spec written
clearly and backed by the Lean, not the Lean shown verbatim, approved the
readable pilot and ruled for explicit pins only.

## Why

The spec must be formal, so that tools and proofs can use it, and readable,
so that people can learn fir from it. Written apart, the two drift. One
source built by CI, and a build that fails when the Lean changes under a
block, keep them together. Verbatim Lean is hard for a newcomer to read.

## Rejected alternatives

- **A spec DSL in the style of Wasm's SpecTec**, generating the Lean, the
  Rust verifier and the document. It is a larger tool than the spec needs. It
  stays open if the hand-written verifier starts to drift.
- **Hiding the Lean without readable blocks.** Doc comments alone read like
  Lean.
- **Readable prose in `lean/`'s doc comments.** `lean/` has no Verso
  dependency, so its doc comments cannot hold the checked directives.
- **Pinning a theorem's pretty-printed statement.** It misses changes to
  definition bodies and constructors.
- **Transitive hashing of every reachable definition.** Almost any change to
  the interpreter would force re-pinning.
- **Everything under `docs/spec/`, or everything under `lean/`.** The first
  moves fir's Lean definitions out of `lean/`. The second leaves `docs/spec/`,
  where readers look for the spec, without the document.
