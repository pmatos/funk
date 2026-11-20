# A global is a core item `global` of units and addresses, valid in its own table

Status: accepted
Tier: direction; area: semantics

## Decision

- **The item.** A global (ADR-2026-11-09-1546) is an item of the core's
  kind `global`, written with the generic item production and an empty body:
  `global @msg() size(8) align(1) const units(104, 105, 0) {` and `}`.
  Its attributes are, in order: `memory(N)` only when `N` is not 0,
  `size(S)`, `align(A)`, the word `const`, the word `export`, then the
  initializer's pieces. Every other order does not decode, so a global has
  one spelling.
- **The initializer.** Pieces fill the global's units in order from its
  first: `units(U, ...)` gives units one by one, `zeros(N)` gives `N` zero
  units, and `addr(@s)` or `addr(@s, K)`, `K` not 0, gives the address of
  the global `@s` plus `K` units. An address takes the units of one
  pointer of `@s`'s memory in the global's memory, as a stored pointer
  does. A unit is any natural number; every other number is at most
  `2^64 - 1`.
- **Validity.** The memory is declared, the alignment is a valid one
  (`MemLayout.ValidAlign`), each unit is below `2^U` for its memory's unit
  width `U`, each `addr` names a global of the item's own table, and the
  initializer takes at most the size. A nested module's globals are its
  own.
- **The words.** The item is `global` and the flag `const`, the words of
  ADR-2026-11-09-1546, as the human ruled on 2026-11-20 (#237 Q4). The
  core's text writes them too (`alloca`'s kind `global`, the op `const`),
  so the G0 check lists both, with `align`, among the words generic code
  shares with the core, on the Lean and the Rust side.
- **What it leaves to the run.** A global is still one allocation of
  kind `global` (ADR-2026-11-09-1546), apart from the kind `function`
  that the human ruled for a function's address on 2026-11-19 (#235).
  Its allocation, its address op and `addr(@f)` of a function come with
  the run's starting allocations in #237's later stages.

## Why

ADR-2026-11-09-1546 fixes what a global holds and leaves the spelling open.
The generic production needs no grammar change, and pieces in order are
what an assembler writes as data and relocations. Checking addresses in
the table keeps an item naming only items of its own table
(ADR-2026-11-10-1510).

## Rejected alternatives

- **Units and relocations at explicit offsets:** two parts that must agree,
  and overlaps to reject.
- **A negative offset in `addr`:** no C address constant needs one.
- **`addr` of a function now:** a function's address is an allocation
  of kind `function` (#235, ruled 2026-11-19), which no run makes yet.
- **The words `data` and `constant`,** which stage 1 shipped so that no
  check changed: neither is a core word, but neither is what the ADR and
  every reader call a global and its flag.
