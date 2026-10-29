import Fir.Core.Types
import Fir.Syntax.Dialect

/-!
The M0 op set: constants, integer arithmetic, bitwise ops and shifts,
comparison and selection, width changes, `freeze`, branches and calls. Each
op below is an op instance: it carries its attributes and the widths it is
used at, so that its operand and result types follow from it.

This chapter gives the ops and their signatures. What each op computes, and
when it yields poison or immediate UB, is stated in prose here and defined in
Lean in the execution rules of its op family (#10 and #14 to #20). In short,
following S1 (ADR-2026-10-29-2006): a flag violation yields poison, a shift
amount `≥ N` yields poison, and division by zero and `INT_MIN / -1` are
immediate UB.
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

* `const w v`: the constant `v` of type `iN`.

Arithmetic. The result wraps modulo `2^N` unless a flag says otherwise:

* `add w f`, `sub w f`, `mul w f`: addition, subtraction and multiplication,
  with the flags `f`.
* `sdiv w exact`, `udiv w exact`: signed and unsigned division, rounding
  towards zero. With `exact`, a non-zero remainder gives poison. A zero
  divisor is immediate UB, and so is `sdiv` of the signed minimum by `-1`.
* `srem w`, `urem w`: the remainders of `sdiv` and `udiv`, with the sign of
  the dividend for `srem`. They have the same UB as the divisions.

Bitwise ops and shifts:

* `and w`, `or w`, `xor w`: bitwise operations.
* `shl w`, `lshr w`, `ashr w`: shift left, logical shift right (filling with
  zeros) and arithmetic shift right (filling with the sign bit). The second
  operand is the shift amount, read as unsigned; an amount `≥ N` gives
  poison.

Comparison and selection:

* `icmp p w`: compares two `iN` values with predicate `p`, giving an `i1`:
  `1` when the predicate holds, `0` when it does not.
* `select w`: takes an `i1` condition and two `iN` values, and gives the
  first value when the condition is `1`, the second when it is `0`.

Width changes:

* `zext m n`: zero-extends an `iM` to an `iN`.
* `sext m n`: sign-extends an `iM` to an `iN`.
* `trunc m n`: keeps the low `N` bits of an `iM`.

Poison control:

* `freeze w`: gives its operand unchanged when it is not poison. When it is
  poison, gives an arbitrary but fixed value: every use of the result sees
  the same bits (S1, ADR-2026-10-29-2017).

Control flow. These ops are the terminators:

* `br`: jumps to its one successor, passing the successor's arguments.
* `condBr`: takes an `i1` condition and has two successors. It jumps to the
  first when the condition is `1` and to the second when it is `0`.
  Branching on poison is immediate UB.
* `ret ts`: returns its operands, of types `ts`, from the function.

Calls:

* `call f ts rs`: calls the function with symbol `f` (H3), passing operands
  of types `ts` and receiving results of types `rs`. Recursion is allowed.
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
