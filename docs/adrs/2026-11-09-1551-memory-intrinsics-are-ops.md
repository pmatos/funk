# Copying, moving and setting memory are ops that keep pointer provenance

Status: accepted
Tier: direction; area: semantics

## Decision

- **Three ops** work over one memory and a length in its units.
  - Copy carries each unit across exactly: bits, poison and pointer fragments
    alike, so a copied pointer keeps its provenance. Overlapping source and
    destination is UB.
  - Move does the same and allows overlap.
  - Set writes one unit value into each unit, sized to the memory's unit: an
    `i8` on the default memory, whose unit is an 8-bit byte unless the data
    layout says otherwise, and an integer of the unit's width on any other.
- **Effects.** Copy and move read the source memory and write the
  destination, and set writes. All three may be UB, for out-of-bounds access
  (ADR-2026-11-09-1541).
- **Frontends** lower a C call to `memcpy` to the copy op, not to an external
  call.
- **Backend.** The naive backend lowers them to funk's own runtime routines
  `memcpy`, `memmove` and `memset`, not the C library's, so a program that
  only copies, moves or sets memory keeps the static link without the C
  library.

[semantics-m1-design.md](../decisions/semantics-m1-design.md) states each
rule. The human ruled this on 2026-11-09, on #220. On 2026-11-11 the human
ruled on #251 that set writes one unit value, and on #274 that funk's runtime
carries its own routines, in place of the C library's that #220 named.

## Why

Frontends emit `memcpy`, `memmove` and `memset` for every struct copy and
initialization. Memory units may be poison or pointer fragments
(ADR-2026-11-09-1542), and a call through the world cannot keep provenance,
so a pointer copied that way would become unusable. As ops, struct copies are
exact in the spec and cheap for passes to recognize.

## Rejected alternatives

- **Calls to external functions with known meanings.** Copies would lose
  provenance, and every copy would be an event of the trace.
- **Set writes a byte into each unit.** A memory's unit need not be a byte.
- **Lower to the C library's routines.** A program that only copies memory
  would need the C library to link.
