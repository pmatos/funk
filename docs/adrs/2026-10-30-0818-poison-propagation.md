# Poison propagates unless an op says otherwise, and every op declares its poison class

Status: accepted

## Context

S1 (ADR-2026-10-29-2006) gives fir one deferred-UB value, poison, with
`freeze`, and makes a branch on poison and a division by zero immediate UB.
It leaves each op's poison rules to the spec. The review of
[PR #29](https://github.com/pmatos/funk/pull/29) found that the spec did not
say what an op does with a poison operand. After a second opinion, the human
ruled on 2026-10-30 to adopt LLVM's rules with two improvements. After an
explanation of poison, UB and `freeze`, the human confirmed that a branch
on poison stays immediate UB (N1 in the [rulings comment](https://github.com/pmatos/funk/issues/5#issuecomment-6506908304) on #5,
part 3).

## Decision

- LLVM's five rules:
  - a poison operand gives a poison result, unless an op says otherwise;
  - `select` with a poison condition gives poison;
  - a poison divisor is immediate UB, because it might be zero;
  - a poison shift amount gives poison;
  - `zext` and `sext` strictly widen, and `trunc` strictly narrows. These
    are validation rules.
- A branch on poison stays immediate UB (S1). It does not go to either
  successor.
- Propagation is checked, not only stated. Every op of every dialect
  declares a poison class through `DialectPoison` (G0): `propagates` or
  `exception`. A propagating op carries the Lean obligation
  `PropagatesPoison`: from operands of which one is poison, every result it
  returns is poison. It may still end in immediate UB by its own rules.
- In the core dialect, 18 ops propagate: `const` (it has no operands), the
  arithmetic, the four divisions, the bitwise ops and shifts, `icmp` and the
  width changes. A division propagates a poison dividend and is UB on a
  poison divisor, which its obligation allows. Six ops are exceptions:
  `select`, `freeze` and `cond_br`, each with its own rule, and `br`, `ret`
  and `call`, which pass values on as they are, to block arguments, the
  caller or the callee.
- The spec states two forbidden rewrites: a `select` becomes a branch only
  with its condition frozen, and `select %c, %x, false` is not
  `and %c, %x` when `%x` may be poison. #16 tests both.
- The spec explains poison, immediate UB, `freeze` and the asymmetry
  between `select` and `cond_br` in plain words
  (`lean/Fir/Execution/PoisonUB.lean`).

## Alternatives

- **A branch on poison goes to either successor.** Rejected: a compiler
  could no longer use what a branch tests. After
  `%c = icmp eq %x, %y; cond_br %c, ...`, replacing `%y` with `%x` in the
  first successor is sound only if a branch on poison is UB.
- **Propagation in prose only**, as LLVM's reference states it. Rejected: an
  op whose execution rules forget to propagate poison would go unnoticed.

## Consequences

- Each ticket that writes an op's execution rules proves `PropagatesPoison`
  for it: #10 for the tracer subset, #14 to #18 for their families. The
  last of them gives `LawfulDialectPoison CoreDialect`. The obligation of
  `const` is already proved.
- An extension dialect declares a class for each of its ops, and proves the
  obligation of each one that propagates.
- Passes must not perform the forbidden rewrites, and the spec says why.
