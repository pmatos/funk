# One emitter owns outgoing funk calls and their stack accounting

Status: accepted

## Context

Fir call lowering and executable entry code both place arguments in
registers and on the stack. Entry stack reservation repeats the padding
calculation. A convention change must keep all three in agreement.

Both callers hold arguments in frame slots relative to `%rbp`, and both
start with a 16-byte-aligned stack. Entry code currently drops outgoing
arguments at its epilogue, while fir call lowering drops them immediately.

## Decision

- `abi::call` emits a complete call from a fir function name and argument
  slots in parameter order. It owns register selection, reverse pushes,
  padding, symbol spelling and cleanup. It moves each slot's bits without
  extension, as ADR-2026-11-02-1021 requires.
- Both callers restore outgoing space immediately after the call. Cleanup
  leaves the result in `%rax` and restores alignment. Entry's later runtime
  printing call uses less stack; its reserved stack figure stays the same.
- The emitter returns its peak outgoing argument bytes, padding included,
  excluding the return address. Entry stack reservation consumes those
  bytes and owns frame sizes, return addresses, runtime space and rounding.
- The emitter checks that cleanup fits a signed 32-bit immediate before
  writing assembly. Its callers retain width checks, located diagnostics
  and result storage or printing.

## Alternatives

- A separate call layout with a cleanup choice preserves today's assembly
  but gives callers a lifetime rule and an argument-count invariant.
- A callback for result handling adds an ordering rule neither caller needs.

## Consequences

- Placement and its accounting share one implementation and one test surface.
- Fir call lowering collects argument slots before emission, so lookup
  failures cannot leave a partially emitted outgoing call.
- Incoming arguments, runtime calls and frame probing retain their existing
  rules (ADR-2026-10-30-1232, ADR-2026-11-02-1102). The emitter is internal
  to the x86-64 crate; no adapter or convention for other targets is added.
