# An aggregate's layout is a core item of placed fields, counted in the units of its memory

Status: accepted
Tier: direction; area: semantics

## Decision

- **The item.** A layout is an item of the core's kind `aggregate`, written
  with the generic item production and an empty body:
  `aggregate @pair() memory(0) size(16) align(8) field(0, i64) field(8, ptr) {`
  and `}`. `field(O, T, C)` is a repeated field of `C` elements. A nested
  module holds layouts of its own.
- **Units.** A field takes the units and alignment that `alloca` gives one
  value of its type in that memory. A repeated field's elements are rounded
  up to that alignment: four `i24` take 16 units of memory 0 (the human's
  ruling of 2026-11-16 on #236, Q2 B).
- **Validity.** The memory is declared, the alignment is valid, each field
  is an integer or a pointer (floats wait for #264) at a multiple of its
  alignment, which is at most the layout's, ends within the size and shares
  no unit with another field.
- **Reading.** A run gives every op's rule a record of its table's
  layouts, with each field's offset and element step (Q1 A). Every law holds
  for every record, so a function's (#235) or a global's (#237) address is
  a new field of it.

## Why

ADR-2026-11-09-1550 makes aggregates layouts over memory, given in the
module and measured in its units, and leaves the spelling open. The generic
production needs no grammar change, and a core kind keeps the word out of
every dialect's namespace (`layout` already starts the data layout line).
Placing fields by alignment is what System V and C need.

## Rejected alternatives

- **A dialect's kind, `core.aggregate`:** the core names no dialect.
- **Elements spaced by their units alone, as `alloca`:** arrays of `i24` or
  `long double` would be misaligned (Q2 A).
- **Offsets and types written at each use (Q1 C):** every use would repeat
  the layout in two parts that must agree.
