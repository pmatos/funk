# Copying, moving and setting memory are ops that keep pointer provenance

Status: accepted
Tier: direction; area: semantics

## Context

Frontends emit `memcpy`, `memmove` and `memset` for every struct copy and
initialization. Memory units may be poison or fragments of a pointer
(ADR-2026-11-09-1542). A call to an external function goes through the
world (ADR-2026-11-09-1540), which cannot preserve provenance: a pointer
copied that way would become unusable, and each call would be an event. The
human ruled on [#220](https://github.com/pmatos/funk/issues/220) on
2026-11-09.

## Decision

- **Three ops.** Copy, move and set work over one memory and a length in
  its units.
  - Copy carries each unit across exactly: bits, poison and pointer
    fragments alike, so a copied pointer keeps its provenance. Overlapping
    source and destination is UB.
  - Move does the same and allows overlap.
  - Set writes one byte value into each unit.
- **Effects.** Copy and move read the source memory and write the
  destination; set writes. All three may be UB, for out-of-bounds access
  (ADR-2026-11-09-1541).
- **Backend.** The naive backend lowers them to calls to the C library's
  `memcpy`, `memmove` and `memset`.

## Alternatives

- **Calls to external functions with known meanings.** Copies would lose
  provenance, and every copy would show up in the trace.

## Consequences

- Struct copies are exact in the spec and cheap to recognize in passes.
- A frontend lowers a C call to `memcpy` to the copy op, not to an external
  call.
