import Fir.Core.Values

/-!
# Constants and addition

The core dialect's execution rules come family by family, one family to a
section, after the definitions that every family shares: the ops, their
signatures, their text, their validation rules and their poison classes.
This section has the rules of `const`, `poison` and `add` without flags;
the next one gives `add` its flags, and `sub` and `mul` their rules.

A rule says what an op computes from values of its operand types. A value
of `iN` is poison or a vector of `N` bits, so each rule says what it does
with poison. A vector of bits exists for every `N`, so one rule serves
every width, from 1 to the largest.

* `const` gives its constant. It has no operands, so it is never poison.
  A float constant gives its bits, at every format, a NaN's payload and
  sign included (ADR-2026-11-11-1438).
* `poison` gives the poison of its type, on every run. It has no operands
  either, so it propagates poison as `const` does: its poison is its own
  rule, not a poison operand's. It is never UB.
* `add` without flags gives the sum of its operands modulo 2^N: it wraps,
  as two's complement does, and it is never UB. A poison operand gives
  poison: `add` propagates poison (ADR-2026-10-30-0818).

Every core op has its rules. What a dialect's semantics does with an op
that has none is in the section on the core op semantics
(`docs/decisions/fir-ref.md#an-op-without-rules`).
-/

namespace Fir.Core

/-- The value of `const w v`: `v`. -/
def constValue (w : Nat) (v : BitVec w) : PoisonOr (BitVec w) := .value v

/-- The value of `fconst e m v`: `v`, the bits of a float of
`float<e,m>`. -/
def fconstValue (e m : Nat) (v : BitVec (floatWidth e m)) : PoisonOr (BitVec (floatWidth e m)) :=
  .value v

/-- The value of `poison w`: the poison of `iN`. -/
def poisonValue (w : Nat) : PoisonOr (BitVec w) := .poison

/-- `add` without flags: the sum modulo `2^N` of two values, and poison when
either operand is poison. -/
def addValues : PoisonOr (BitVec w) → PoisonOr (BitVec w) → PoisonOr (BitVec w)
  | .value a, .value b => .value (a + b)
  | _, _ => .poison

-- A sum wraps, in every width.
#guard addValues (.value (127 : BitVec 8)) (.value 1) == .value (-128)
#guard addValues (.value (1 : BitVec 1)) (.value 1) == .value 0
#guard addValues (.value (-1 : BitVec 33)) (.value 2) == .value 1
-- A poison operand gives poison.
#guard addValues (.poison : PoisonOr (BitVec 8)) (.value 1) == .poison
#guard addValues (.value (1 : BitVec 8)) .poison == .poison

end Fir.Core
