import Fir.Core.Types
import Fir.Syntax.Dialect

/-!
The M0 op set: constants, integer arithmetic, bitwise ops and shifts,
comparison and selection, width changes, `freeze`, branches and calls. Each
op below is an op instance: it carries its attributes and the widths it is
used at, so that its operand and result types follow from it.

This chapter gives the ops and their signatures. What each op computes, and
when it yields poison or immediate UB, is stated in prose here and defined in
Lean in the execution rules of its op family (#10 and #14 to #20). The
execution chapter explains poison and immediate UB in plain words.

# Poison and UB in short

These rules follow S1 (ADR-2026-10-29-2006) and LLVM, as ADR-2026-10-30-0818
records them:

* A poison operand gives a poison result, unless the op says otherwise. The
  ops that say otherwise are `select`, `freeze`, the terminators and `call`;
  the execution chapter lists each op's poison class.
* A broken flag (`nuw`, `nsw`, `exact`) gives poison.
* A shift amount `≥ N` gives poison, and so does a poison shift amount.
* A zero divisor is immediate UB, and so is a poison divisor, because it
  might be zero. `sdiv` or `srem` by `-1` is immediate UB when the dividend
  is the signed minimum, and when it is poison, because it might be the
  signed minimum. Otherwise, a poison dividend gives poison.
* `select` with a poison condition gives poison.
* A branch on poison is immediate UB.

The UB of a poison divisor, and of a poison dividend by `-1`, follows from
one principle of LLVM's reference (LangRef, "Poison Values"; Alive2's
`div_ub` agrees): a poison operand is immediate UB wherever some value it
could take would be UB.
-/

namespace Fir.Core

/--
The flags of `add`, `sub` and `mul`. Each one is a promise about the
operands; when it is broken, the result is poison.

* `nuw` (no unsigned wrap): the operands, read as unsigned integers, give a
  result that fits in `N` bits.
* `nsw` (no signed wrap): the operands, read as two's-complement signed
  integers, give a result that fits in `N` bits.
-/
structure WrapFlags where
  nuw : Bool := false
  nsw : Bool := false
  deriving Repr, DecidableEq, Inhabited

/--
The predicate of an integer comparison. `eq` and `ne` compare bits. The `s`
predicates read the operands as signed integers, the `u` predicates as
unsigned: `lt` is less than, `le` less or equal, `gt` greater than and `ge`
greater or equal.
-/
inductive Pred where
  | eq | ne | slt | sle | sgt | sge | ult | ule | ugt | uge
  deriving Repr, DecidableEq, Inhabited

/--
An op instance of the core dialect. `w` is the width `N` of the integers the
op works on.

Constants:

* `const w v`: the constant `v` of type `iN`. It has no operands, so it is
  never poison.

Arithmetic. The result wraps modulo `2^N` unless a flag says otherwise:

* `add w f`, `sub w f`, `mul w f`: addition, subtraction and multiplication,
  with the flags `f`.
* `sdiv w exact`, `udiv w exact`: signed and unsigned division, rounding
  towards zero. With `exact`, a non-zero remainder gives poison. A zero or
  poison divisor is immediate UB. `sdiv` by `-1` is immediate UB when the
  dividend is the signed minimum or poison. Otherwise a poison dividend
  gives poison.
* `srem w`, `urem w`: the remainders of `sdiv` and `udiv`, with the sign of
  the dividend for `srem`. They have the same UB and poison as the
  divisions: `srem` by `-1` is immediate UB when the dividend is the signed
  minimum or poison, and `urem` is UB only on a zero or poison divisor.

Bitwise ops and shifts:

* `and w`, `or w`, `xor w`: bitwise operations.
* `shl w`, `lshr w`, `ashr w`: shift left, logical shift right (filling with
  zeros) and arithmetic shift right (filling with the sign bit). The second
  operand is the shift amount, read as unsigned; an amount `≥ N` gives
  poison, and so does a poison amount.

Comparison and selection:

* `icmp p w`: compares two `iN` values with predicate `p`, giving an `i1`:
  `true` when the predicate holds, `false` when it does not.
* `select w`: takes an `i1` condition and two `iN` values, and gives the
  first value when the condition is `true`, the second when it is `false`.
  A poison condition gives poison. The value not chosen does not matter,
  even when it is poison; the one chosen is given as it is, poison or not.

Width changes:

* `zext m n`: zero-extends an `iM` to an `iN`, where `M < N`.
* `sext m n`: sign-extends an `iM` to an `iN`, where `M < N`.
* `trunc m n`: keeps the low `N` bits of an `iM`, where `N < M`.

Poison control:

* `freeze w`: gives its operand unchanged when it is not poison. When it is
  poison, gives an arbitrary but fixed value: every use of the result sees
  the same bits (S1, ADR-2026-10-29-2006; ADR-2026-10-29-2017).

Control flow. These ops are the terminators:

* `br`: jumps to its one successor, passing the successor's arguments. A
  poison argument arrives as poison.
* `condBr`: takes an `i1` condition and has two successors. It jumps to the
  first when the condition is `true` and to the second when it is `false`.
  Branching on poison is immediate UB.
* `ret ts`: returns its operands, of types `ts`, from the function: any
  number of values, each a value or poison (ADR-2026-10-30-0816).

Calls:

* `call f ts rs`: calls the function with symbol `f` (H3), passing operands
  of types `ts` and receiving results of types `rs`, any number of each.
  Poison passes through: a poison operand is a poison argument, and a
  poison that the callee returns is a poison result. Recursion is allowed.
-/
inductive Op where
  | const (w : Nat) (v : BitVec w)
  | add (w : Nat) (f : WrapFlags)
  | sub (w : Nat) (f : WrapFlags)
  | mul (w : Nat) (f : WrapFlags)
  | sdiv (w : Nat) (exact : Bool)
  | udiv (w : Nat) (exact : Bool)
  | srem (w : Nat)
  | urem (w : Nat)
  | and (w : Nat)
  | or (w : Nat)
  | xor (w : Nat)
  | shl (w : Nat)
  | lshr (w : Nat)
  | ashr (w : Nat)
  | icmp (p : Pred) (w : Nat)
  | select (w : Nat)
  | zext (m n : Nat)
  | sext (m n : Nat)
  | trunc (m n : Nat)
  | freeze (w : Nat)
  | br
  | condBr
  | ret (ts : List Ty)
  | call (f : String) (ts rs : List Ty)
  deriving Repr, DecidableEq

end Fir.Core
