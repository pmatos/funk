import Fir.Core.Types
import Fir.Syntax.Dialect

/-!
The core dialect's ops: constants, integer arithmetic, bitwise ops and
shifts, comparison and selection, width changes, `freeze` and `poison`,
branches and calls, and the float constants, comparisons, arithmetic, bit
casts, conversions from integers and conversions between formats.
Each op below is an op instance: it carries its
attributes and the widths it is used at, so that its operand and result
types follow from it.

This chapter gives the ops and their signatures. What each op computes, and
when it yields poison or immediate UB, is stated in prose here and defined in
Lean in the execution rules of its op family, in the sections _Arithmetic
rules_ to _Call rules_ of the execution chapter. The execution chapter
explains poison and immediate UB in plain words.

# Poison and UB in short

These rules follow the poison semantics of ADR-2026-10-29-2006 and LLVM, as
that ADR records them:

* A poison operand gives a poison result, unless the op says otherwise. The
  ops that say otherwise are `select`, `freeze`, the terminators and `call`;
  the execution chapter lists each op's poison class.
* `poison` gives poison on every run: it is how a program writes a poison
  value.
* A broken flag (`nuw`, `nsw`, `exact`) gives poison.
* A shift amount `≥ N` gives poison, and so does a poison shift amount.
* A zero divisor is immediate UB, and so is a poison divisor, because it
  might be zero. `sdiv` or `srem` by `-1` is immediate UB when the dividend
  is the signed minimum, and when it is poison, because it might be the
  signed minimum. Otherwise, a poison dividend gives poison.
* `select` with a poison condition gives poison.
* A branch on poison is immediate UB.
* Reaching `unreachable` is immediate UB.

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
The predicate of a float comparison, as LLVM names it. An `o` predicate is
ordered: it is false when either operand is a NaN. A `u` predicate is
unordered: it is true when either operand is a NaN. Otherwise each compares
the numbers that the operands encode, so `-0` equals `+0`: `eq` is equal,
`ne` not equal, `lt` less than, `le` less or equal, `gt` greater than and
`ge` greater or equal. `ord` holds when neither operand is a NaN, and `uno`
when either is (ADR-2026-11-09-1549).
-/
inductive FPred where
  | oeq | one | olt | ole | ogt | oge | ord
  | ueq | une | ult | ule | ugt | uge | uno
  deriving Repr, DecidableEq, Inhabited

/--
A float op of two operands (ADR-2026-11-09-1549): `fadd` adds, `fsub`
subtracts the second operand from the first, `fmul` multiplies and `fdiv`
divides the first by the second, each rounded to nearest even. `frem` and
`fmod` give the remainder of the first by the second, `x - n * y`, which
is exact, so they do not round: `frem`'s `n` is the quotient rounded to
nearest, ties to even, IEEE 754's remainder, and `fmod`'s is the quotient
truncated, C's `fmod` and LLVM's `frem` (#310).
-/
inductive FBin where
  | fadd | fsub | fmul | fdiv | frem | fmod
  deriving Repr, DecidableEq, Inhabited

/--
A float op of one operand (ADR-2026-11-09-1549): `fneg` negates, `fabs`
gives the absolute value, and `sqrt` the square root, rounded to nearest
even. Only `sqrt` rounds: a negation or an absolute value is a float of
the format.
-/
inductive FUnary where
  | fneg | fabs | sqrt
  deriving Repr, DecidableEq, Inhabited

/--
An op instance of the core dialect. `w` is the width `N` of the integers the
op works on.

Constants:

* `const w v`: the constant `v` of type `iN`. It has no operands, so it is
  never poison.

* `fconst e m v`: the constant `v` of the float type `float<e,m>`, given
  by its bits: a sign bit, `e` exponent bits and `m` mantissa bits. Every
  bit pattern is a constant, each NaN's payload and sign included. It has
  no operands, so it is never poison (ADR-2026-11-11-1438).

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
* `fcmp p e m`: compares two values of `float<e,m>` with predicate `p`,
  giving an `i1`, by the numbers they encode in Lean's float model. It is
  never UB, and a poison operand gives poison (ADR-2026-11-09-1549).

Float arithmetic, by Lean's float model, with a NaN result that is any NaN
of the format (ADR-2026-11-09-1549). Each is never UB, and a poison operand
gives poison:

* `fbin o e m`: the op `o`, `fadd`, `fsub`, `fmul`, `fdiv`, `frem` or
  `fmod`, of two values of `float<e,m>`; all but `frem` and `fmod`, whose
  result is exact, round to nearest even.
* `funary o e m`: the op `o`, `fneg`, `fabs` or `sqrt`, of one value of
  `float<e,m>`; `sqrt` rounds to nearest even.
* `fma e m`: `a * b + c` of three values of `float<e,m>`, rounded once,
  to nearest even.

Width changes:

* `zext m n`: zero-extends an `iM` to an `iN`, where `M < N`.
* `sext m n`: sign-extends an `iM` to an `iN`, where `M < N`.
* `trunc m n`: keeps the low `N` bits of an `iM`, where `N < M`.

Bit casts, which read the same bits as another type
(ADR-2026-11-09-1549):

* `toBits e m`: the bits of a value of `float<e,m>`, as an `iN` with
  `N = 1 + e + m`. A NaN's sign and payload come through as they are.
* `ofBits e m`: the bits of an `iN`, with `N = 1 + e + m`, as a value of
  `float<e,m>`.

Each is never UB, and a poison operand gives poison.

Conversions from an integer to a float, by Lean's float model
(ADR-2026-11-09-1549):

* `sitofp n e m`: the integer that an `iN` holds, read as signed, as a
  value of `float<e,m>`, rounded to nearest even.
* `uitofp n e m`: the integer that an `iN` holds, read as unsigned, as a
  value of `float<e,m>`, rounded to nearest even.

A result too large for the format is an infinity of its sign, and zero
gives `+0`. Neither is ever UB or gives a NaN, and a poison operand gives
poison.

Conversions between two float formats, by Lean's float model
(ADR-2026-11-09-1549; the human's ruling of 2026-11-12 on #354):

* `fpext e m e' m'`: a value of `float<e,m>` as a value of
  `float<e',m'>`, where `e ≤ e'` and `m ≤ m'`, so the target holds every
  value of the source and nothing rounds.
* `fptrunc e m e' m'`: a value of `float<e,m>` rounded, to nearest even,
  into `float<e',m'>`, a format that cannot hold every value of the
  source: `e' < e` or `m' < m`.

Every ordered pair of two formats takes exactly one of them, and a format
to itself takes neither. Zeros and infinities keep their sign, and a NaN
gives any NaN of the target. Neither is ever UB, and a poison operand gives
poison.

Poison control:

* `freeze w`: gives its operand unchanged when it is not poison. When it is
  poison, gives an arbitrary but fixed value: every use of the result sees
  the same bits (S1, ADR-2026-10-29-2006; ADR-2026-10-29-2017).
* `poison w`: the poison of type `iN`. Like `const`, it has no operands,
  but it has no attributes either, and its result is poison on every run.
  Native code may give any value of `iN` in its place, since every value
  refines poison (S4).

Control flow. These ops are the terminators:

* `br`: jumps to its one successor, passing the successor's arguments. A
  poison argument arrives as poison.
* `condBr`: takes an `i1` condition and has two successors. It jumps to the
  first when the condition is `true` and to the second when it is `false`.
  Branching on poison is immediate UB.
* `ret ts`: returns its operands, of types `ts`, from the function: any
  number of values, each a value or poison (ADR-2026-10-29-2008).
* `unreachable`: has no operands and no successors, and reaching it is
  immediate UB (ADR-2026-11-09-1548). A producer puts it where control
  never goes, such as after a call that never returns.

Calls:

* `call f ts rs`: calls the function with symbol `f` (H3), passing operands
  of types `ts` and receiving results of types `rs`, any number of each.
  Poison passes through: a poison operand is a poison argument, and a
  poison that the callee returns is a poison result. Recursion is allowed.
-/
inductive Op where
  | const (w : Nat) (v : BitVec w)
  | fconst (e m : Nat) (v : BitVec (floatWidth e m))
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
  | fcmp (p : FPred) (e m : Nat)
  | fbin (o : FBin) (e m : Nat)
  | funary (o : FUnary) (e m : Nat)
  | fma (e m : Nat)
  | select (w : Nat)
  | zext (m n : Nat)
  | sext (m n : Nat)
  | trunc (m n : Nat)
  | toBits (e m : Nat)
  | ofBits (e m : Nat)
  | sitofp (n e m : Nat)
  | uitofp (n e m : Nat)
  | fpext (e m e' m' : Nat)
  | fptrunc (e m e' m' : Nat)
  | freeze (w : Nat)
  | poison (w : Nat)
  | br
  | condBr
  | ret (ts : List Ty)
  | unreachable
  | call (f : String) (ts rs : List Ty)
  deriving Repr, DecidableEq

end Fir.Core
