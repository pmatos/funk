# fieldaddr moves a pointer to a field of a layout that it names

Status: accepted
Tier: direction; area: semantics

## Decision

- **The op.** The core op `fieldaddr` names an aggregate's layout by its
  symbol and one of its fields by its number, counted from 0, and takes a
  pointer, and for an element of a repeated field an index of any `iW`:
  `%q: ptr = fieldaddr @pair 1 %p` and `%e: ptr = fieldaddr @row 0 %p, %k`.
  Its result is a pointer of the pointer's memory.
- **The rule.** The result is the pointer moved by the field's offset, plus
  the index, read as signed, times the element's units rounded up to its
  alignment (ADR-2026-11-16-1546). The rule reads the layout from the items
  that the run gives every op (the human's ruling of 2026-11-16 on #236,
  Q1 A), keeps the pointer's provenance, and is never UB: an index outside
  the field's elements is an address, as `ptradd` gives one (Q3 A). A
  poison operand gives poison, and the op is pure.
- **Every record.** The laws hold for every record of items a run may give,
  with no hypothesis: a record without the layout or the field moves the
  pointer by 0. Validation keeps a valid module from naming one, and the
  run gives each op the layout validation checked (`RunItems.ofTable_ref`).
- **Validation.** The symbol names a layout of the op's own table, in the
  pointer's memory; the field is one of its fields; and only a repeated
  field takes an index. A repeated field named with no index gives its
  first element.

## Why

ADR-2026-11-09-1550 asks for one op that computes a field's or element's
address from a pointer and a layout. Attributes come before operands in
every op's text, as `call @f %x` writes its callee, so the symbol and the
field lead. A field number, not an offset, keeps one spelling per field and
lets validation reject a field the layout does not have.

## Rejected alternatives

- **The offset and the field's type written at each use (Q1 C):** two parts
  that must agree with the layout.
- **Poison or UB for an index out of range (Q3 B and C):** one-past-the-end
  pointers and flexible array members would need `ptradd` instead.
- **A rule that is UB for a record without the layout:** every law would
  need a hypothesis on the record, so the #384 guarantees would gain one.
