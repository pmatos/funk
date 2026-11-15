import Fir.Core.OpAttrs
import Fir.Core.Types
import Fir.Memory.Model
import Fir.Memory.Ordering
import Fir.Syntax.Dialect

/-!
The core dialect's ops: constants, integer arithmetic, bitwise ops and
shifts, comparison and selection, width changes, `freeze` and `poison`,
branches and calls, the float constants, comparisons, arithmetic, bit
casts, conversions from integers, conversions between formats and
conversions to integers, pointer offsets, stack allocation, loads and
stores.
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
* A broken flag (`nuw`, `nsw`, `exact`, `nnan`, `ninf`) gives poison.
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
* `fcmp p fl e m`: compares two values of `float<e,m>` with predicate `p`,
  giving an `i1`, by the numbers they encode in Lean's float model. It is
  never UB, and a poison operand gives poison (ADR-2026-11-09-1549). With
  the flag `nnan` a NaN operand, and with `ninf` an infinite one, gives
  poison; `nsz` has nothing to act on, since the result is not a float.

Float arithmetic, by Lean's float model, with a NaN result that is any NaN
of the format (ADR-2026-11-09-1549). Each is never UB, and a poison operand
gives poison. Each carries the fast-math flags `fl`: a broken `nnan` or
`ninf` gives poison, and with `nsz` a zero result has either sign. Each
op that rounds carries a rounding mode `r` (`RoundingMode`). M1's
validation accepts only `rne`, round to nearest even, and the rules read
every mode as `rne`, since no valid module carries another:

* `fbin o fl e m`: the op `o`, `fadd`, `fsub`, `fmul`, `fdiv`, `frem` or
  `fmod`, of two values of `float<e,m>`; all but `frem` and `fmod`, whose
  result is exact, round, with the mode that `o` carries.
* `funary o fl e m`: the op `o`, `fneg`, `fabs` or `sqrt`, of one value of
  `float<e,m>`; `sqrt` rounds, with the mode that it carries.
* `fma fl r e m`: `a * b + c` of three values of `float<e,m>`, rounded once,
  with the mode `r`.

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

* `sitofp r n e m`: the integer that an `iN` holds, read as signed, as a
  value of `float<e,m>`, rounded with the mode `r`.
* `uitofp r n e m`: the integer that an `iN` holds, read as unsigned, as a
  value of `float<e,m>`, rounded with the mode `r`.

Validation accepts only the mode `rne`, round to nearest even, and the
rules read every mode as `rne`.

A result too large for the format is an infinity of its sign, and zero
gives `+0`. Neither is ever UB or gives a NaN, and a poison operand gives
poison.

Conversions between two float formats, by Lean's float model
(ADR-2026-11-09-1549; the human's ruling of 2026-11-12 on #354):

* `fpext e m e' m'`: a value of `float<e,m>` as a value of
  `float<e',m'>`, where `e ≤ e'` and `m ≤ m'`, so the target holds every
  value of the source and nothing rounds.
* `fptrunc r e m e' m'`: a value of `float<e,m>` rounded, with the mode
  `r`, into `float<e',m'>`, a format that cannot hold every value of the
  source: `e' < e` or `m' < m`. Validation accepts only the mode `rne`,
  and the rule reads every mode as `rne`.

Every ordered pair of two formats takes exactly one of them, and a format
to itself takes neither. Zeros and infinities keep their sign, and a NaN
gives any NaN of the target. Neither is ever UB, and a poison operand gives
poison.

Pointer offsets (#231):

* `ptradd n w`: moves a pointer of `ptr<N>`, `N = n`, by the integer that
  an `iW`, `W = w`, holds, read as signed, in units of the memory `N`. It
  keeps the pointer's provenance, and its offset may leave the bounds of
  the allocation: only an access through it must be in bounds
  (ADR-2026-11-13-0251). It is never UB, and a poison operand gives
  poison.

Stack allocation (#231; the human's ruling of 2026-11-14 on #378):

* `alloca k t c a n`: allocates room for `c` values of the type `t` in the
  memory `n`, with the kind `k`, and gives a pointer of `ptr<N>`, `N = n`,
  to the first unit of the allocation. It takes `c` times the units of `t`
  in that memory, aligned to `a` units, or to the natural alignment of `t`
  when `a` is `none`. A stack allocation is freed when the call that made
  it returns. Its units are poison until a store writes them. It is never
  UB, never gives poison, and allocates in the memory `n`. M1's validation
  accepts only the kind `stack`, a count of at least 1, an alignment that
  is a power of two no larger than `MemLayout.limit`, and an integer or
  pointer type `t`; the count has no bound (ADR-2026-11-14-0915).

Loads (#231):

* `load o w a n`: loads an `iW`, `W = w`, through a pointer of `ptr<N>`,
  `N = n`, with the ordering `o`, as an access aligned to `a` units, or to
  the natural alignment of `iW` in the memory `N` when `a` is `none`. It
  reads the units that `iW` takes in that memory and decodes them: units
  that are not the encoding of an integer, as a poison unit or a pointer's
  fragment, give poison. A poison pointer is immediate UB, since some
  pointer in its place faults, and so is an access that faults: out of
  bounds, to a freed allocation, through a pointer without provenance, or
  misaligned. It reads its memory, may be UB and may give poison. M1's
  validation accepts only the ordering `nonatomic`, and an alignment that
  is a power of two no larger than `MemLayout.limit`.

Stores (#231):

* `store o w a n`: stores a value of `iW`, `W = w`, through a pointer of
  `ptr<N>`, `N = n`, with the ordering `o`, as an access aligned as a
  `load`'s is, and gives no result. It writes the encoding of the value in
  the units that `iW` takes in the memory `N`: zero padding past `W` bits,
  and poison units for a poison value. A poison pointer is immediate UB,
  as for `load`, and so is an access that faults. It writes its memory and
  may be UB. Validation accepts what it accepts of a `load`.

Loads and stores of pointers (#231; the human's ruling of 2026-11-14 on
#382):

* `loadPtr o m a n`: loads a `ptr<M>`, `M = m`, through a pointer of
  `ptr<N>`, `N = n`, as `load` loads an integer: the units that a pointer
  of memory `M` takes in memory `N`, decoded as a pointer. Only the
  fragments of one pointer of memory `M`, in order, give that pointer;
  any other units give poison. Its effects are `load`'s.
* `storePtr o m a n`: stores a `ptr<M>` through a pointer of `ptr<N>`, as
  `store` stores an integer: the pointer's fragments, or poison units for
  poison. Its effects are `store`'s.

With no alignment, either access is aligned to the default alignment of
`ptr<M>` in memory `N`, as an `alloca` of `ptr<M>` is.

Conversions from a float to an integer, by Lean's float model
(ADR-2026-11-09-1549; the human's ruling of 2026-11-12 on #354):

* `fptosi e m n`: a value of `float<e,m>` truncated toward zero, as a
  signed integer of `iN`.
* `fptoui e m n`: a value of `float<e,m>` truncated toward zero, as an
  unsigned integer of `iN`.

An integer that `iN` does not hold, an infinity and a NaN give poison.
Neither is ever UB, and a poison operand gives poison.

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
  | fcmp (p : FPred) (fl : FastMath) (e m : Nat)
  | fbin (o : FBin) (fl : FastMath) (e m : Nat)
  | funary (o : FUnary) (fl : FastMath) (e m : Nat)
  | fma (fl : FastMath) (r : RoundingMode) (e m : Nat)
  | select (w : Nat)
  | zext (m n : Nat)
  | sext (m n : Nat)
  | trunc (m n : Nat)
  | toBits (e m : Nat)
  | ofBits (e m : Nat)
  | sitofp (r : RoundingMode) (n e m : Nat)
  | uitofp (r : RoundingMode) (n e m : Nat)
  | fpext (e m e' m' : Nat)
  | fptrunc (r : RoundingMode) (e m e' m' : Nat)
  | ptradd (n w : Nat)
  | alloca (k : Memory.AllocKind) (t : Ty) (c : Nat) (a : Option Nat) (n : Nat)
  | load (o : Memory.Ordering) (w : Nat) (a : Option Nat) (n : Nat)
  | store (o : Memory.Ordering) (w : Nat) (a : Option Nat) (n : Nat)
  | loadPtr (o : Memory.Ordering) (m : Nat) (a : Option Nat) (n : Nat)
  | storePtr (o : Memory.Ordering) (m : Nat) (a : Option Nat) (n : Nat)
  | fptosi (e m n : Nat)
  | fptoui (e m n : Nat)
  | freeze (w : Nat)
  | poison (w : Nat)
  | br
  | condBr
  | ret (ts : List Ty)
  | unreachable
  | call (f : String) (ts rs : List Ty)
  deriving Repr, DecidableEq

end Fir.Core
