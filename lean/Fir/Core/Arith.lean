import Fir.Core.Values

/-!
# Constants and addition

The core dialect's execution rules come family by family, one family to a
section, behind the definitions that every family shares: the op set, its
signature, its text, its validation rules and its poison classes. Ticket
#10 gives the rules of its tracer subset: `const`, `add` without flags, and
`ret`. This section has the first two, and #14 adds the flags of `add`, and
`sub` and `mul`.

A rule says what an op computes from values of its operand types. A value
of `iN` is `PoisonOr (BitVec N)`, so each rule says what it does with
poison. `BitVec N` exists for every `N`, so one rule serves every width,
from 1 to `maxWidth`.

* `const w v` gives `v`. It has no operands, so it is never poison.
* `add w` without flags gives the sum of its operands modulo `2^N`: it
  wraps, as two's complement does, and it is never UB. A poison operand
  gives poison: `add` propagates poison (ADR-2026-10-30-0818).

What the dialect's semantics does with ops whose family has no rules yet,
`add` with a flag among them, is the next section's.
-/

namespace Fir.Core

/-- The value of `const w v`: `v`. -/
def constValue (w : Nat) (v : BitVec w) : PoisonOr (BitVec w) := .value v

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
