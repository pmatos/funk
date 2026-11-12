# A WebAssembly backend is milestone M8

Status: accepted
Tier: direction; area: process

## Decision

- **M8 is "WebAssembly backend".** Its epic is #293 and its GitHub milestone
  is "M8: WebAssembly backend". The epic is split into tasks later. The number
  only follows M7; it does not set the order of work.
- **Wasm version.** The most recent WebAssembly version, with the proposals
  accepted into it.
- **Two targets.** wasm32 has 32-bit pointers. wasm64 (memory64) has 64-bit
  pointers.
- **Host references** such as `externref` and `funcref` are target extension
  types, as in LLVM's `TargetExtType` (#292). They are not a kind of `ptr<N>`.
- **Testing.** The harness runs the output with wasmtime and checks that its
  results refine `fir-ref`'s. This approves wasmtime as new tooling for this
  milestone.

The human ruled on 2026-11-11, in #292 and #293, that the backend is a new
milestone, and settled the version, the targets, host references and
wasmtime. The human approved the roadmap change, PR #304. Still open: how
fir's control-flow graph lowers to Wasm's structured blocks and loops, the
detailed design of #292, and M8's order relative to M2 to M7.

## Why

A second kind of backend tests G0: Wasm is a stack machine with structured
control flow, several memories and values owned by the host, none of which
x86-64 or arm64 has.

## Rejected alternatives

- **Host references as a kind of `ptr<N>`, as LLVM's non-integral address
  spaces.** A host reference is not a pointer into a fir memory and cannot be
  stored in one, which fir's non-integral flag does not express. The human
  chose a family of types that a target or dialect names (#292).
