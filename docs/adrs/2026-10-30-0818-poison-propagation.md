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
part 3). Part 4 of the rulings settled two questions that this left open:
a poison dividend of `sdiv` or `srem` by `-1`, and what `PropagatesPoison`
must check.

## Decision

- LLVM's five rules:
  - a poison operand gives a poison result, unless an op says otherwise;
  - `select` with a poison condition gives poison;
  - a poison divisor is immediate UB, because it might be zero;
  - a poison shift amount gives poison;
  - `zext` and `sext` strictly widen, and `trunc` strictly narrows. These
    are validation rules.
- `sdiv` and `srem` by `-1` are immediate UB when the dividend is poison,
  because it might be the signed minimum, as they are when it is the signed
  minimum (part 4).
- Both division rules come from one principle of LLVM's reference: a poison
  operand is immediate UB wherever some value it could take would be UB
  (LangRef, "Poison Values"; Alive2's `div_ub` in `ir/instr.cpp` agrees).
  So the x86-64 backend (#18) can emit a bare `idiv`.
- A branch on poison stays immediate UB (S1). It does not go to either
  successor.
- Propagation is checked, not only stated. Every op of every dialect
  declares a poison class through `DialectPoison` (G0): `propagates` or
  `exception`. A propagating op carries the Lean obligation
  `PropagatesPoison`, with two clauses:
  - from operands of which one is poison, every result it returns is
    poison;
  - it is UB on such operands only by its own rules: only if it is UB on
    some operands that put a defined value in place of each poison and
    agree with them elsewhere. This is the principle above, in Lean.
- Every op of every dialect, of either class, is also total and monotone.
  Total: it has an outcome on every operand vector, and a terminator's exit
  has one too. Monotone: refining its operands refines what it does, with a
  poison value refined by every value of its type. Both look only at what
  runs: the semantics of an op that is not a terminator, and the exit of a
  terminator. Monotonicity makes refinement compositional: replacing one
  part of a function with a part that refines it refines the whole
  function. For `call`, whose meaning comes from #20's call effect, the
  op-level obligations are a stand-in, and #20 proves their counterparts at
  function level.
- A propagating op also returns a result on some operand vector with no
  poison. Without this, an op that is always UB would meet both poison
  clauses, since UB would be its own rule. Exceptions are exempt, so an
  exception that is always UB, such as a future `unreachable`, stays
  allowed. `LawfulDialectPoison` holds all of these obligations.
- In the core dialect, 18 ops propagate: `const` (it has no operands), the
  arithmetic, the four divisions, the bitwise ops and shifts, `icmp` and the
  width changes. A division is UB on a poison divisor, `sdiv` and `srem`
  are UB on a poison dividend by `-1`, and every other poison dividend
  gives poison. The second clause allows both kinds of UB, and rejects UB
  on a poison operand of every other propagating op. Six ops are exceptions:
  `select`, `freeze` and `cond_br`, each with its own rule, and `br`, `ret`
  and `call`, which pass values on as they are, to block arguments, the
  caller or the callee.
- The spec states two forbidden rewrites: a `select` becomes a branch only
  with its condition frozen, and `select %c, %x, false` is not
  `and %c, %x` when `%x` may be poison. #16 tests the `and` rewrite and
  #19 the `cond_br` one.
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
- **An obligation on returned results only.** Rejected: an `add` that turns
  a poison operand into UB, or into no outcome, would meet it, and that
  would undo the deferral that poison exists for.
- **A poison dividend by `-1` gives poison.** Rejected by the human
  (part 4): `sdiv` would not be monotone, since refining that poison to the
  signed minimum turns a result into UB, and a backend would need a guard
  before every `idiv`.

## Consequences

- Each ticket that writes an op's execution rules proves its obligations:
  #10 for the tracer subset (`const`, `add`, `ret`), #14 to #20 for their
  families. The last of them gives `LawfulDialectPoison CoreDialect`. The
  poison clauses and the monotonicity of `const` are already proved; its
  totality and its result on defined operands wait for #10.
- Theorems in `lean/Fir/Core/Unlawful.lean` check that the obligations
  reject an op with no outcome, an `add` that is UB on a poison operand,
  the rejected `sdiv` rule, and a semantics in which every op is always UB.
  The obligations do not fix what an op computes: each family's semantics
  does.
- An extension dialect declares a class for each of its ops, and proves the
  obligation of each one that propagates.
- Passes must not perform the forbidden rewrites, and the spec says why.
