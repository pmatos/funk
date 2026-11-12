# Each op declares a set of effects, named by memory, and the spec proves the declaration sound

Status: accepted; refined by ADR-2026-11-11-0801
Tier: direction; area: semantics

## Decision

- **A set of effects.** Each op declares a set drawn from: reads memory *m*,
  writes memory *m*, allocates or frees in memory *m*, may-UB, may produce
  poison, observable and control. The empty set is pure. May produce poison
  means that some result may be poison on operands with no poison; the
  poison class sits beside the set, in the one class `DialectEffects`.
- **Named by memory.** Reads, writes, allocation and freeing name the memory
  they touch, and effects on different memories commute. An external call,
  an indirect call to an unknown function and inline assembly without a narrower declaration carry
  every effect on every memory that can have escaped to them.
- **Declared by the dialect,** for its own ops and the memories it adds, in
  Lean and in Rust's `OpSpec`. Rust's sets are checked against Lean's.
- **Proved sound.** For each effect an op leaves out, the spec proves the
  obligation: an op without a write to *m* keeps the units of *m*, one
  without may-UB never ends in UB, and so on. The obligations are stated
  over the op's semantics with memory, wherever a run names the dialect's
  memories.
- **Calls.** A call's effects are its own rule's and its callee's summary:
  the join of every effect but control of each op the callee may reach,
  computed per symbol table and proved sound.

[semantics-effects.md](../decisions/semantics-effects.md) states what holds,
the obligations and the human's rulings: #208 (2026-11-09) and #226, option B
(2026-11-10). semantics-m1-design.md says how M1's ops are classified.

## Why

Passes need one proved place to read what an op may do. A load reads memory,
may hit UB and may produce poison at once, so one class per op is too coarse.
G0 asks for several memories, and a write to one should not block reordering
with a read of another.

## Rejected alternatives

- **One class per op,** as the decision record proposed. A load would lose
  its may-UB or fall into a catch-all class.
- **Effect sets that do not name a memory.** Accesses to different memories
  could never be reordered.
- **May produce poison is the poison class.** `const`, `icmp` and `add`
  without flags would be marked as producing poison.
- **A call carries control.** Every call would claim to be a terminator.
