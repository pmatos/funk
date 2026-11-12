# Deferred UB is one poison value with `freeze`, and fir has no `undef`

Status: accepted; refined by ADR-2026-11-05-1715
Tier: direction; area: semantics

## Decision

- fir has one deferred-UB value, **poison**, plus the `freeze` op. There is no
  `undef`. `freeze` of poison yields an arbitrary but fixed value: every use
  of the result sees the same value.
- The flags `nsw`, `nuw` and `exact` turn their failure into poison, and so
  does a shift amount `>= N`. Division by zero, `INT_MIN / -1` and a branch on
  poison are immediate UB.
- Poison propagates by LLVM's rules unless an op says otherwise. A poison
  operand is immediate UB wherever some value it could take would be UB: a
  poison divisor, and a poison dividend of `sdiv` or `srem` by `-1`.
- Every op of every dialect declares a poison class, `propagates` or
  `exception`, and the spec proves the obligations of `LawfulDialectPoison`:
  propagation, a result on some operands with no poison for a propagating op,
  totality and monotonicity. They cover only op instances whose types
  validation accepts, and totality and monotonicity only ops that run by their
  own rule: a call has none, since its meaning is its callee's run.
- The core dialect writes poison with the op `poison`, of class `propagates`.

[semantics-poison.md](../decisions/semantics-poison.md) states each rule, the
core's classes and the human's rulings: S1 on #5 (2026-10-29), parts 3 and 4
of the rulings on #5 (2026-10-30), #20 and #69 (2026-11-02) and #122
(2026-11-03).

## Why

A failure that defers its UB lets the op that caused it still be moved or
speculated. One deferred value, used consistently, keeps rewrites sound.
Declaring and proving each op's class means that an op whose rules forget
poison fails to build, rather than going unnoticed.

## Rejected alternatives

- **`undef` as well as poison** (LLVM). Uses of one `undef` may disagree:
  `mul %x, 2` is even, but `add %x, %x` can be odd.
- **A branch on poison goes to either successor.** A compiler could no
  longer use what a branch tests.
- **Propagation in prose only.** A forgotten rule would go unnoticed.
- **A poison dividend by `-1` gives poison.** `sdiv` would not be monotone,
  and every `idiv` would need a guard.
