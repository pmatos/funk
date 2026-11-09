# Current decisions: semantics, effects

This page continues semantics.md. It says what holds today about the effects
of ops. It summarizes the ADRs it cites and does not replace them. When this
page and an ADR disagree, the page is wrong (ADR-2026-11-09-1610).

## Effect sets

Each op declares a set of effects, drawn from this list
(ADR-2026-11-09-1541):

- reads memory `m`, writes memory `m`, and allocates or frees in memory `m`;
- may-UB;
- may produce poison;
- observable: it adds an event to the trace;
- control: it is a terminator.

The empty set is pure. The memory-named effects name the dialect's memories,
or every memory, as an external call needs. Their shape is fixed, and no op
uses them yet: the core dialect has no memory, so its memories have no names
(ADR-2026-11-09-1541, ADR-2026-11-09-1542).

An op may produce poison when, on some operands with no poison, a result may
be poison. That is not the poison class, which says how an op treats poison
operands. `select` is a poison exception and makes no poison from defined
operands, and `add` propagates poison and makes some only with a flag
(ADR-2026-11-09-2249).

The Lean class `DialectEffects`, in `lean/Fir/Execution/OpEffects.lean`, gives
each op its poison class and its effect set. `DialectPoison` folded into it
(ADR-2026-11-09-1541, ADR-2026-11-09-2249). An op's set holds the effects of
its own rule. An op with a callee also has its callee's, since its meaning is
the callee's run (ADR-2026-11-02-1514).

## The core ops' sets

`Core.Op.effects`, in `lean/Fir/Core/OpEffects.lean`, lists each core op by
its constructor, with no case for the rest. `scripts/check_g0.py` checks that,
as it checks `Core.Op.poisonClass` (ADR-2026-11-03-0600). The sets
(ADR-2026-11-09-1541, ADR-2026-11-09-2249):

- Pure: `const`, `and`, `or`, `xor`, `icmp`, `select`, the width changes,
  `freeze`, and `add`, `sub` and `mul` without flags. `call`'s own set is
  empty.
- May produce poison: `poison`, the shifts, `add`, `sub` and `mul` with a
  flag, and `sdiv` and `udiv` with `exact`.
- May-UB: the four divisions and `cond_br`.
- Control: `br`, `cond_br` and `ret`.

## Soundness

`LawfulDialectEffects`, in `lean/Fir/Execution/EffectLaws.lean`, holds the
obligations of each effect an op leaves out (ADR-2026-11-09-1541):

- Without may-UB, the op never ends in UB, and neither does a terminator's
  exit.
- Without may produce poison, the op gives no poison on operands with no
  poison.
- Without control, the op is not a terminator.

The first two cover valid op instances that are terminators or have no
callee, as the poison obligations do (ADR-2026-11-02-1514). The memory-named
effects and observable have no obligation yet: M0's runs have no memory and no
trace. The core dialect is lawful in its effects
(`Core.lawfulDialectEffects`), and `lean/FirTest/G0.lean` restates the class
and its obligations for every dialect. The toy test dialect declares its
effects through the class and is lawful in them.
