# A function's address is a zero-size allocation that funcaddr gives

Status: accepted
Tier: direction; area: semantics

## Decision

- **The value.** A function's address is a pointer to an allocation of the
  kind `function`: one per function of a table, in memory 0, with no
  units, made when a run starts and live for the whole run. A load or a
  store through it is UB. `ptr_expose` and comparison work as for data.
  The human ruled this on 2026-11-19, on #235 (Q1).
- **The run's start.** Memory 0 starts with the table's globals of memory
  0 (ADR-2026-11-19-0124), then one constant allocation, aligned to 1, for
  each function of the table, in the table's order.
- **The op.** `%p: ptr = funcaddr @f` takes no operands and gives the
  pointer to `@f`'s allocation, at offset 0. It is valid when `@f` names a
  function of the op's own table, as `call` resolves its callee, and its
  result is `ptr`, memory 0. It is pure. An external declaration is not a
  function, so `funcaddr` does not name one yet.
- **The extent.** A `function` block of no units takes one address, so
  two functions exposed get different addresses. Every other block takes
  its units.

## Why

The ruling keeps "a pointer is an allocation id and an offset" of
ADR-2026-11-09-1542, so every memory law covers function pointers with no
new case. Functions after the globals keep every global's id, and so every
`addr` piece's units. One address per function is the least that gives
distinct functions distinct addresses.

## Rejected alternatives

- **The kind `global`, a pointer carrying the code address, or a
  provenance naming a symbol:** ruled out on 2026-11-19.
- **Functions before the globals:** every global's id would move.
- **One op, `addressof @f`, for globals and functions:** its validity
  would depend on the item's kind, where `globaladdr` already names
  globals alone.
