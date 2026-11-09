# The core dialect writes poison with `poison`, a constant op of class `propagates`

Status: accepted
Tier: direction; area: semantics

## Context

S1 (ADR-2026-10-29-2006) gives fir one deferred-UB value, poison, but no
way to write it: a program got poison only from an op's rule, such as a
broken flag or a shift by `N` or more. The ports of LLVM's tests stood in
for LLVM's `poison` constant with `shl %n, %n` (ADR-2026-11-03-0644).

The human ruled on 2026-11-03, by dialog, that the core dialect gains a
poison constant now, in M0
([#122](https://github.com/pmatos/funk/issues/122)). It is a new core op,
written like `const`, `%p: i32 = poison @0`, with no operands and no
attributes, whose result is poison of its written type. The human chose it
over a reserved operand `%poison`, because it needs no change to the
generic grammar. Native code may lower it to any value (S4). The Lean
definitions are the normative spec (P1). The ruling adds this op and
changes nothing else of fir's semantics or syntax.

Every op declares a poison class (ADR-2026-10-30-0818). A propagating op
must also return a result on some operand vector with no poison
(`ReturnsOnDefined`), and the design notes on #122 asked whether `poison`,
which never returns a defined value, can meet that.

## Decision

- **The op.** `poison w` is the 25th core op (`Op.poison` in
  `lean/Fir/Core/Ops.lean`), listed under poison control beside `freeze`,
  as the epic lists it. It is written `%p: iN = poison @L`: its name, no
  attributes, no operands. `Op.decode` reads it only with no attributes,
  no operands and one `iN` result. Validation has no rule for it beyond
  its signature: its result type must be valid, `iN` with
  `1 ≤ N ≤ maxWidth`, as for `const`.
- **Its rule.** It gives the poison of `iN` on every run
  (`poisonValue`). It is never UB and makes no choice. Its rule sits
  beside `const`'s, in the section on constants
  (`lean/Fir/Core/Arith.lean`), and its obligations beside `const`'s.
- **Its class is `propagates`.** The obligations admit it, as they admit
  `const`. No operand vector of `poison` holds a poison, so both poison
  clauses hold. `ReturnsOnDefined` asks for a result on some operand
  vector with no poison, not for a defined result: the empty vector holds
  no poison, and on it `poison` returns its one result. That obligation
  rejects an op that is always UB, and `poison` never is UB. It is total
  and monotone, as `const` is. So 19 core ops propagate poison and six
  are exceptions. `LawfulDialectPoison CoreDialect` holds with no
  `sorry` and only the standard axioms.
- **Rust.** `funk-ir` registers `poison` beside `const`
  (`dialects/core/constant.rs`), and both printers write the same bytes
  for it.

This refines S1 and ADR-2026-10-30-0818: poison can now be written, and
the class list gains one op. How the backend lowers it, how G0's check
reads its name, how the coverage matrix counts it and how the LLVM ports
use it are ADR-2026-11-03-1616, ADR-2026-11-03-1617,
ADR-2026-11-03-1618 and ADR-2026-11-03-1619.

## Alternatives

- **A reserved operand `%poison`.** Rejected by the human: it changes
  the generic grammar.
- **Class `exception`.** The obligations admit it too, with fewer of
  them. But an exception states its own rule for poison operands, and
  `poison` has no operands; `propagates` asks more of it and holds.

## Consequences

- Every count of the core op set is 25, and every proof by cases over
  `Op` has a case for `poison`.
- A program, a test or a ported case writes poison directly, at any
  width, with no op whose rule happens to give it.
