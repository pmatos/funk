# A WebAssembly backend is milestone M8

Status: accepted
Tier: direction; area: process

## Context

The roadmap plans backends for x86-64 (M0, M2) and arm64 (needed by M7)
only. On 2026-11-11 the human proposed WebAssembly as a target for funk
(#293). A second kind of backend tests G0: Wasm is a stack machine with
structured control flow, several memories and values owned by the host,
none of which x86-64 or arm64 has. The same day the human ruled that the
backend is a new milestone, with #293 as its epic, and settled its main
choices on #292 and #293.

## Decision

- **M8 is "WebAssembly backend".** Its epic is #293 and its GitHub
  milestone is "M8: WebAssembly backend". The epic is split into tasks
  later. The number only follows M7; it does not set the order of work.
- **Wasm version.** The most recent WebAssembly version, with the
  proposals accepted into it.
- **Two targets.** wasm32 has 32-bit pointers. wasm64 (memory64) has
  64-bit pointers.
- **Host references** such as `externref` and `funcref` are target
  extension types, as in LLVM's `TargetExtType` (#292). They are not a
  kind of `ptr<N>`.
- **Testing.** The harness runs the output with wasmtime and checks that
  its results refine `fir-ref`'s. This approves wasmtime as new tooling
  for this milestone.

## Consequences

- `docs/roadmap.md` lists M8 with its scope. The deferred decisions
  moved to `docs/roadmap-deferred.md` to keep the roadmap within the file
  budget.
- Still open: how fir's control-flow graph lowers to Wasm's structured
  blocks and loops, the detailed design of #292, and M8's order relative
  to M2 to M7.
