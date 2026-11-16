# An aggregate's layout is a core item of placed fields, counted in the units of its memory

Status: accepted
Tier: direction; area: semantics

## Decision

- **The item.** A layout is an item of the core's kind `aggregate`, written
  with the one production of an item and an empty body:
  `aggregate @pair() memory(0) size(16) align(8) field(0, i64) field(8, ptr) {`
  and `}` on the next line. `memory(N)`, `size(S)` and `align(A)` come
  first, in that order, then `field(O, T)`, or `field(O, T, C)` for `C`
  repeated elements; every number is at most `2^64 - 1`. A nested module
  holds layouts of its own, in the symbol space of its items.
- **Units.** A field of type `T` in memory `N` takes the units and the
  natural alignment that `alloca` gives one `T` there
  (`Core.Ty.fieldShape_eq_allocaShape`); a dialect says so of its types
  through `DialectValidation.fieldShape`. A repeated field takes `C` times
  one element's units rounded up to its alignment: four `i24` in memory 0
  take 16 units (the human's ruling of 2026-11-16 on #236, Q2 B).
- **Validity.** The module declares `N`; `A` is a valid alignment; each
  field type is valid, names declared memories and may be a field (an
  integer or a pointer in the core; floats wait for #264); each field's
  offset is a multiple of its alignment, which is at most `A`, and it ends
  within `S`; no two fields share a unit, so a field of no units, a C
  flexible array member, overlaps nothing.
- **Reading.** A run gives every op's rule a record of its module's items,
  beside each memory's layout entry: each layout of the function's table,
  with each field's offset and the step between its elements (the human's
  ruling of 2026-11-16 on #236, Q1 A). Every law over the semantics with
  memory holds for every record, so a function's (#235) or a global's
  (#237) address is a new field of it.

## Why

ADR-2026-11-09-1550 makes aggregates layouts over memory, given in the
module and measured in the units of their memory, and leaves the spelling
open. The generic production writes the item with no grammar change, and a
core kind keeps the word out of every dialect's namespace (`layout` already
starts the data layout line). Placing each field by its type's alignment is
what System V classification and C need.

## Rejected alternatives

- **An item of a dialect's kind,** `core.aggregate`: the core names no
  dialect, and its typed fields would stay generic attributes.
- **Elements spaced by the type's units,** as `alloca`: arrays of `i24` or
  `long double` would be misaligned (#236, Q2 A).
- **Offsets and types written at each use** (#236, Q1 C): every use would
  repeat what the layout says, in two parts that must agree.
