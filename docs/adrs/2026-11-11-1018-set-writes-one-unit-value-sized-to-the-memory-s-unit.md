# Setting memory writes one unit value, sized to the memory's unit

Status: accepted
Tier: direction; area: semantics

## Context

ADR-2026-11-09-1551 has the set op write "one byte value into each unit".
Under ADR-2026-11-09-1542 a memory's unit of addressing is an 8-bit byte
only unless the data layout says otherwise, so a unit need not be a byte
([#251](https://github.com/pmatos/funk/issues/251)). The human ruled on #251
on 2026-11-11.

## Decision

- Set writes one unit value into each unit of its range. The value is sized
  to the memory's unit: an `i8` on the default memory, and an integer of the
  unit's width on a memory whose unit is wider or narrower.

This refines ADR-2026-11-09-1551's set.

## Consequences

- Set works the same way on every memory, whatever its unit.
- The memory intrinsics ticket
  ([#234](https://github.com/pmatos/funk/issues/234)) gives set's value
  operand the memory's unit width.
