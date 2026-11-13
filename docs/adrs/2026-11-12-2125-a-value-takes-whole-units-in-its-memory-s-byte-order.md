# A value takes whole units of its memory, placed in the memory's byte order

Status: accepted
Tier: direction; area: semantics

## Decision

- **Integers.** A value of `iN` takes `ceil(N / U)` units of a memory whose
  units are `U` bits wide: its digits in base `2^U`. When `N` is not a
  multiple of `U`, a store sets the bits past `N` to zero, and a load
  ignores them, whatever they hold: an `i1` loaded from the byte `0xFF` is
  1, with no UB and no poison.
- **Pointers.** A value of `ptr<N>` takes `ceil(P / U)` units, where `P` is
  the pointer width of memory `N` in the data layout. Each unit holds one
  fragment of the pointer and the memory number `N`. So a pointer copied
  unit by unit keeps its provenance.
- **Poison.** Poison takes the same number of units, each one poison. A
  load from units of which any is poison gives poison.
- **Punned and partial loads.** A load gives poison when its units are not
  the encoding of a value of its type: an integer from a pointer's
  fragments, and a `ptr<N>` from anything but one pointer's fragments of
  memory `N`, in order. An integer copy of memory therefore carries no
  pointer: a pointer loaded from the copy is poison.
- **Byte order.** The units are placed in the memory's byte order: `little`
  puts the least significant first. The encoding and decoding laws take the
  byte order as a parameter and hold at every order; M1's layouts admit only
  `little` (ADR-2026-11-12-1821).

The human ruled odd widths, punned loads and the byte-order parameter on
2026-11-11, on #231.

## Why

ADR-2026-11-09-1542 makes memory abstract units, but leaves how a value
becomes units open. Loads and stores in the spec, `fir-ref` and every
backend must agree on it. Zero padding gives each value one encoding, so a
store is deterministic and memories compare unit by unit, and ignoring the
padding lets a backend load whole units and truncate. Poison for a punned
load keeps provenance out of integers, which ADR-2026-11-09-1542 allows only
through `ptr.expose`, and the memory in each fragment keeps a pointer in its
memory, which it leaves only through an op.

## Rejected alternatives

- **Reject widths that are not a multiple of the unit.** `i1` and `i20`
  could never be stored, and every frontend would widen them first.
- **Padding bits that a store leaves unspecified.** A store would become a
  choice, which multiplies exhaustive runs for no observable difference.
- **Immediate UB for a punned load.** Copying memory as integers would
  become UB even when the copied value is never used.
