import Fir.Core.Values
import Fir.Core.Text

/-!
# Comparison and selection

Ticket #16 gives `icmp` and `select` their rules. Neither is ever UB.

`icmp p` takes two values of `iN` and gives an `i1`: `true` when the
predicate `p` holds of them, and `false` when it does not. `eq` and `ne`
compare the bits. The `s` predicates read both operands as
two's-complement signed integers, and the `u` predicates read them as
unsigned integers, so one pair of bit patterns can be in one order for
`slt` and in the other for `ult`. At `i8`, `-1` is less than `1` read as
signed, but it is `255` read as unsigned, which is greater. At `i1`,
`true` is `-1` read as signed and `1` read as unsigned, so
`icmp slt true, false` gives `true` and `icmp ult true, false` gives
`false`.

`icmp` propagates poison (ADR-2026-10-30-0818): a poison operand gives a
poison `i1`. So `icmp eq %p, %p` of a poison `%p` is poison, not `true`.

`select c, a, b` takes an `i1` condition and two values of `iN`, and gives
one of them: `a` when `c` is `true`, and `b` when it is `false`. It is an
exception to poison propagation, with a rule of its own
(ADR-2026-10-30-0818):

* A poison condition gives poison.
* The value not chosen does not matter, even when it is poison.
* The value chosen is given as it is, poison or not.

So a `select` gives poison only through its condition or the value it
chooses. That is why `select %c, %x, false` is not `and %c, %x`, as the
section on poison and immediate UB explains: when `%c` is `false`, the
`select` gives `false` whatever `%x` is, and the `and` gives poison when
`%x` is poison.

The predicates are `==` on bits and Lean's own `BitVec.slt`, `BitVec.sle`,
`BitVec.ult` and `BitVec.ule`, which compare `BitVec.toInt` and
`BitVec.toNat`. `sgt`, `sge`, `ugt` and `uge` are `slt`, `sle`, `ult` and
`ule` with the operands swapped. `true` is the `i1` value `1`.
-/

namespace Fir.Core

/-- Whether the predicate holds of two values of `iN`. -/
def Pred.holds : Pred → BitVec w → BitVec w → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .slt, a, b => a.slt b
  | .sle, a, b => a.sle b
  | .sgt, a, b => b.slt a
  | .sge, a, b => b.sle a
  | .ult, a, b => a.ult b
  | .ule, a, b => a.ule b
  | .ugt, a, b => b.ult a
  | .uge, a, b => b.ule a

/-- `icmp p`: `true` when the predicate `p` holds of two values, `false`
when it does not, and poison when either operand is poison. -/
def icmpValues (p : Pred) : PoisonOr (BitVec w) → PoisonOr (BitVec w) → PoisonOr (BitVec 1)
  | .value a, .value b => .value (.ofBool (p.holds a b))
  | _, _ => .poison

/-- `select`: the first value when the condition is `true` and the second
when it is `false`, each as it is, poison or not; poison when the condition
is poison. -/
def selectValues :
    PoisonOr (BitVec 1) → PoisonOr (BitVec w) → PoisonOr (BitVec w) → PoisonOr (BitVec w)
  | .value c, a, b => if c = 1 then a else b
  | .poison, _, _ => .poison

/-! # Tests

Each predicate on pairs of values at `i1`, `i7`, `i8`, `i33`, `i64` and
`i128`, among them the boundary values `0`, `1`, all ones (`-1`), the
signed minimum and the signed maximum, and pairs whose signed order is not
their unsigned order. -/

/-- What the ten predicates give, in the order of `Pred.all`, on two values
that are in the order `s` read as signed and in the order `u` read as
unsigned. -/
def predResults (s u : Ordering) : List Bool :=
  [s == .eq, s != .eq, s == .lt, s != .gt, s == .gt, s != .lt,
   u == .lt, u != .gt, u == .gt, u != .lt]

/-- `icmp` gives, with each predicate, what `predResults s u` says on the
values `a` and `b`. -/
def comparesAs (a b : BitVec w) (s u : Ordering) : Bool :=
  Pred.all.map (icmpValues · (.value a) (.value b)) ==
    (predResults s u).map fun r => .value (.ofBool r)

-- At `i8`, `-1` is less than `1` read as signed, and greater read as
-- unsigned.
#guard icmpValues .slt (.value (-1 : BitVec 8)) (.value 1) == .value 1
#guard icmpValues .ult (.value (-1 : BitVec 8)) (.value 1) == .value 0
#guard icmpValues .ugt (.value (-1 : BitVec 8)) (.value 1) == .value 1
#guard icmpValues .eq (.value (5 : BitVec 8)) (.value 5) == .value 1

-- At `i1`, `true` is `-1` read as signed and `1` read as unsigned.
#guard comparesAs (1 : BitVec 1) 0 .lt .gt
#guard comparesAs (0 : BitVec 1) 1 .gt .lt
#guard comparesAs (1 : BitVec 1) 1 .eq .eq
#guard comparesAs (0 : BitVec 1) 0 .eq .eq

/-- Pairs of values of `iN`, for `N ≥ 3`, each with its order read as signed
and its order read as unsigned. -/
def boundaryPairs (w : Nat) : List (BitVec w × BitVec w × Ordering × Ordering) :=
  [(0, 0, .eq, .eq), (0, 1, .lt, .lt), (1, 0, .gt, .gt), (-1, 0, .lt, .gt), (0, -1, .gt, .lt),
   (-1, 1, .lt, .gt), (-1, -1, .eq, .eq), (.intMin w, .intMax w, .lt, .gt),
   (.intMax w, .intMin w, .gt, .lt), (.intMin w, 0, .lt, .gt), (.intMax w, -1, .gt, .lt),
   (.intMin w, -1, .lt, .lt), (1, .intMax w, .lt, .lt), (.intMin w, .intMin w, .eq, .eq)]

-- At `i7`, `i8`, `i33`, `i64` and `i128`.
#guard [7, 8, 33, 64, 128].all fun w => (boundaryPairs w).all fun (a, b, s, u) => comparesAs a b s u
-- Some of them spelled out: at `i7`, `-64` is the signed minimum and `63`
-- the signed maximum.
#guard comparesAs (-64 : BitVec 7) 63 .lt .gt && comparesAs (63 : BitVec 7) (-1) .gt .lt
#guard comparesAs (-128 : BitVec 8) 127 .lt .gt && comparesAs (-128 : BitVec 8) (-1) .lt .lt
#guard comparesAs (-4294967296 : BitVec 33) 4294967295 .lt .gt
#guard comparesAs (-9223372036854775808 : BitVec 64) 9223372036854775807 .lt .gt
#guard comparesAs (2 : BitVec 128) (-2) .gt .lt

-- A poison operand gives poison, with every predicate, in either place.
-- So `icmp eq` of poison with itself is poison.
#guard [1, 8, 33].all fun w => Pred.all.all fun p =>
  icmpValues p .poison (.value (0 : BitVec w)) == .poison &&
    icmpValues p (.value (-1 : BitVec w)) .poison == .poison &&
    icmpValues (w := w) p .poison .poison == .poison

/-! `select` at each width: `true` chooses the first value and `false` the
second. -/

#guard selectValues (.value 1) (.value (0 : BitVec 1)) (.value 1) == .value 0
#guard selectValues (.value 0) (.value (0 : BitVec 1)) (.value 1) == .value 1
#guard selectValues (.value 1) (.value (BitVec.intMin 7)) (.value (BitVec.intMax 7)) ==
  .value (BitVec.intMin 7)
#guard selectValues (.value 0) (.value (BitVec.intMin 7)) (.value (BitVec.intMax 7)) ==
  .value (BitVec.intMax 7)
#guard selectValues (.value 1) (.value (-1 : BitVec 8)) (.value 1) == .value (-1)
#guard selectValues (.value 0) (.value (-1 : BitVec 8)) (.value 1) == .value 1
#guard selectValues (.value 1) (.value (BitVec.intMax 33)) (.value 0) == .value (BitVec.intMax 33)
#guard selectValues (.value 0) (.value (BitVec.intMax 64)) (.value (BitVec.intMin 64)) ==
  .value (BitVec.intMin 64)
#guard selectValues (.value 1) (.value (BitVec.intMin 128)) (.value (-1)) ==
  .value (BitVec.intMin 128)

/-! `select` and poison. -/

-- A poison condition gives poison, even when both values are the same.
#guard selectValues .poison (.value (7 : BitVec 8)) (.value 7) == .poison
#guard selectValues (w := 1) .poison .poison .poison == .poison
-- The value not chosen does not matter, even when it is poison.
#guard selectValues (.value 1) (.value (7 : BitVec 8)) .poison == .value 7
#guard selectValues (.value 0) .poison (.value (BitVec.intMin 64)) == .value (BitVec.intMin 64)
#guard selectValues (.value 1) (.value (1 : BitVec 1)) .poison == .value 1
-- The value chosen is given as it is, poison included.
#guard selectValues (.value 1) .poison (.value (7 : BitVec 8)) == .poison
#guard selectValues (.value 0) (.value (7 : BitVec 33)) .poison == .poison
#guard selectValues (w := 128) (.value 1) .poison .poison == .poison

end Fir.Core
