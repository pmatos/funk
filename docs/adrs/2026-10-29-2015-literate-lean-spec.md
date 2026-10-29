# The spec is literate Lean, rendered with Verso

Status: accepted

## Context

This is decision P1, made on 2026-10-29 after the other rows of the fir v0
decision record, and stated in the M0 epic
([#5](https://github.com/pmatos/funk/issues/5)) and the roadmap.

Great documentation of fir is a first-class deliverable. The spec must be
formal, so that tools and proofs can use it, and readable, so that people can
learn fir from it. When the formal and the readable spec are written apart,
they drift. The semantics of fir lives in Lean (S7, ADR-2026-10-29-2009).

## Decision

- The spec keeps the Wasm spec's chapters: abstract syntax, validation,
  execution and text format.
- It is written as literate Lean. The Lean definitions are the normative spec.
  The prose beside them makes it readable by a person.
- Verso, Lean's documentation tool, renders definitions and prose together as
  the readable document. CI builds it on every PR, so the readable and the
  formal spec cannot drift.
- No change to fir's semantics merges without its spec section, formal and
  readable.
- The Rust verifier is hand-written and tested against Lean.

### Where it lives

- **`lean/`** is the Lean package. It holds every Lean definition of fir. The
  spec's chapters live there as literate Lean modules, with prose beside the
  definitions; the execution chapter's definitions are the reference
  interpreter. The package also holds the `.fir` parser and printer, the
  proofs and the `fir-ref` executable.
- **`docs/spec/`** is the Verso document. It holds the document's entry point,
  the order of its chapters and any prose that belongs to no single
  definition. It renders the literate Lean from `lean/`, and it adds no
  definition that the semantics depends on.
- The rendered document is a build output and is not committed.
- How Lake and Verso are wired together, and how the Lean toolchain is pinned,
  is decided in [#8](https://github.com/pmatos/funk/issues/8) and recorded in
  its Lean toolchain ADR.

## Alternatives

- **A spec DSL in the style of Wasm's SpecTec**, generating the Lean
  definitions, the Rust verifier and the document from one source. Not used.
  It can still come later if the hand-written verifier starts to drift.
- **Everything under `docs/spec/`.** It would move fir's Lean definitions,
  including the interpreter, out of `lean/`, where the epic places the Lean
  semantics.
- **Everything under `lean/`.** It would leave `docs/spec/`, where `AGENTS.md`
  and the roadmap send readers for the spec, without the document.

## Consequences

- A change to fir's semantics edits Lean definitions and their prose in the
  same PR, and CI shows the rendered result.
- CI needs the Lean toolchain and Verso, and builds the document through a
  hook in `.pre-commit-config.yaml`.
- The Rust verifier can drift from the Lean validation rules. The differential
  harness catches that: `funk verify` and the Lean validation rules must agree
  on every corpus module.
