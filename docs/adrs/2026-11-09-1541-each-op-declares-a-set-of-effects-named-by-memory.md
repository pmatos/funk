# Each op declares a set of effects, named by memory, and the spec proves the declaration sound

Status: accepted
Tier: direction; area: semantics

## Context

This is decision H7 of the fir v0 decision record, which marks it
Foundational. In M0 an op is either pure or a call, and every op declares
its poison class through `DialectPoison`
([`Propagation.lean`](../../lean/Fir/Execution/Propagation.lean),
ADR-2026-11-03-0600).

The record proposed one effect class per op: pure, may-produce-poison,
reads memory, writes memory, may-UB or control. One class is too coarse
once memory exists: a load reads memory, may hit UB and may produce poison,
all at once. With several memories (G0, ADR-2026-11-09-1542), a write to one
memory should not block reordering with a read of another. The human ruled
on [#208](https://github.com/pmatos/funk/issues/208) on 2026-11-09.

## Decision

- **A set of effects.** Each op declares a set drawn from:
  - reads memory *m*;
  - writes memory *m*;
  - allocates or frees in memory *m*;
  - may-UB;
  - may produce poison, which is the op's existing poison class;
  - observable: it adds an event to the trace (ADR-2026-11-09-1540);
  - control: it is a terminator.

  The empty set is pure.
- **Named by memory.** Reads, writes, allocation and freeing name the
  memory they touch. Effects on different memories commute. An external
  call, an indirect call to an unknown function and inline assembly without
  a narrower declaration carry every effect on every memory that can have
  escaped to them.
- **Declared by the dialect.** A new Lean class, beside `DialectPoison`,
  gives each op's effect set, and `OpSpec` gives it in Rust. A dialect
  declares the effects of its own ops, including effects on memories it
  adds.
- **Proved sound.** For each op, the spec proves that its declaration
  over-approximates its semantics:
  - an op that does not declare a write to *m* leaves *m* unchanged;
  - one without may-UB never ends in UB;
  - one without observable adds no event;
  - and so on for each effect.

  Passes may rely on a declaration because of that proof. The Rust
  registry's declarations are checked against the Lean ones, as op
  signatures are.
- **The classification.** Every core op of M0 is pure, may produce poison
  or may-UB, as its rules already say, and `call` carries the callee's
  effects. Each M1 op is classified when it lands, in its own ticket, by the
  same rule: loads read and may-UB; stores write and may-UB; stack
  allocation allocates; memory intrinsics read and write
  (ADR-2026-11-09-1551); volatile accesses are also observable; external
  calls and inline assembly are observable; `unreachable` and tail calls
  are control.
- The aegraph stays an optimizer view outside the spec. may-UB is the hook
  that will cover `assume`.

## Alternatives

- **One class per op, as the record proposed.** A load would lose its
  may-UB or fall into a catch-all class, and passes would need special
  cases.
- **Effect sets that do not name a memory.** Accesses to different
  address spaces could never be reordered, which undercuts the reason G0
  asks for several memories.

## Consequences

- M2's passes read effects from one place, and the reading is proved.
- Each new op costs one soundness proof per effect it leaves out.
- `DialectPoison` folds into the effect class when the class lands.
