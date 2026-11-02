import Fir.Core.Values

/-!
# Division and remainder

Ticket #18 gives `sdiv`, `udiv`, `srem` and `urem` their rules. `sdiv` and
`udiv` divide, rounding towards zero; `srem` and `urem` give the remainder
of that division, which for `srem` has the sign of the dividend. The `s`
ops read their operands as two's-complement signed integers, the `u` ops
as unsigned ones. They are ops whose failure the hardware cannot defer,
so, with a branch on poison, they are the core ops with immediate UB
(ADR-2026-10-30-0818):

* A zero divisor is immediate UB, and so is a poison divisor, because it
  might be zero.
* `sdiv` and `srem` by `-1` are immediate UB when the dividend is the
  signed minimum, whose quotient does not fit in `N` bits, and when it is
  poison, because it might be the signed minimum. That holds for `srem`
  too, although its result would be `0`: x86-64's `idiv` traps on it.
* Otherwise a poison dividend gives poison. That includes `udiv` and
  `urem` by all ones, which have no `-1` case.

The human ruled the poison dividend by `-1` on 2026-10-30. UB there keeps
every division monotone, and lets a backend emit a bare `idiv` or `div`,
with no guard. The rejected rule, a poison result, is not monotone, as
`Core.Unlawful.oldSDiv_unlawful` shows.

`exact` is a flag of `sdiv` and `udiv` only. It promises that the division
leaves no remainder; when it does, the result is poison, not UB (S1,
ADR-2026-10-29-2006). It is checked only on two values that are not UB, so
a division that is UB with `exact` is UB without it.

Each UB has a reason that names its op and its case, such as
`sdiv by zero` or `srem of poison by -1`. Reasons are for people:
refinement ignores them. At `i1` the values are `false` and `true`, and
`true` is `-1`, the signed minimum and all ones at once. So `sdiv` and
`srem` of `true` by `true` are UB, and `udiv` and `urem` of a poison by
`true` give poison.

A division ends in one of two ways, with a result or with UB, and never
chooses. So its rule is a function, `divEv`, to `Ev`, the ways a
computation of the set monad may end; `ruleOfEv` then makes it a rule in
any monad with the UB effect, as the core dialect's semantics asks. Lean's
`BitVec.sdiv`, `BitVec.udiv`, `BitVec.srem` and `BitVec.umod` compute the
results, and the rule calls them only on a divisor that is not zero.
-/

namespace Fir.Core

/-- How a division or remainder ends on two operands, as the rules above
say. `name` is the op's name, which every UB reason starts with. `signed`
says that the op reads its operands as signed, so that a dividend divided
by `-1` can be the signed minimum. `q a b` is the op's result on two
values, a divisor that is not zero, and no signed minimum by `-1`. -/
def divEv (name : String) (signed : Bool) (q : BitVec w → BitVec w → PoisonOr (BitVec w)) :
    PoisonOr (BitVec w) → PoisonOr (BitVec w) → Ev (PoisonOr (BitVec w))
  | _, .poison => .ub s!"{name} by poison"
  | .poison, .value b =>
    if b = 0 then .ub s!"{name} by zero"
    else if signed ∧ b = -1 then .ub s!"{name} of poison by -1"
    else .ok .poison
  | .value a, .value b =>
    if b = 0 then .ub s!"{name} by zero"
    else if signed ∧ a = BitVec.intMin w ∧ b = -1 then
      .ub s!"{name} of the signed minimum by -1"
    else .ok (q a b)

/-- `sdiv`, with or without `exact`: the quotient rounded towards zero,
and poison when `exact` is broken. -/
def sdivWith (exact : Bool) :
    PoisonOr (BitVec w) → PoisonOr (BitVec w) → Ev (PoisonOr (BitVec w)) :=
  divEv "sdiv" true fun a b => if exact ∧ a.srem b ≠ 0 then .poison else .value (a.sdiv b)

/-- `udiv`, with or without `exact`: the quotient rounded down, and poison
when `exact` is broken. -/
def udivWith (exact : Bool) :
    PoisonOr (BitVec w) → PoisonOr (BitVec w) → Ev (PoisonOr (BitVec w)) :=
  divEv "udiv" false fun a b => if exact ∧ a.umod b ≠ 0 then .poison else .value (a.udiv b)

/-- `srem`: the remainder of `sdiv`, with the sign of the dividend. -/
def sremValues : PoisonOr (BitVec w) → PoisonOr (BitVec w) → Ev (PoisonOr (BitVec w)) :=
  divEv "srem" true fun a b => .value (a.srem b)

/-- `urem`: the remainder of `udiv`. -/
def uremValues : PoisonOr (BitVec w) → PoisonOr (BitVec w) → Ev (PoisonOr (BitVec w)) :=
  divEv "urem" false fun a b => .value (a.umod b)

/-- The rule, in any monad with the UB effect, of an op that takes two
values of `iN`, gives one, and ends as `g` says: with that result, or with
immediate UB. -/
def ruleOfEv {m : Type → Type} [Monad m] [MonadUB m]
    (g : PoisonOr (BitVec w) → PoisonOr (BitVec w) → Ev (PoisonOr (BitVec w))) :
    HVector toType [i w, i w] → m (HVector toType [i w])
  | .cons a (.cons b .nil) => match g a b with
    | .ok v => pure (.cons v .nil)
    | .ub r => MonadUB.ub r

-- Lean's operations round towards zero, and `srem` takes the dividend's
-- sign, as these ops ask.
#guard (BitVec.sdiv (-7 : BitVec 8) 2, BitVec.srem (-7 : BitVec 8) 2) == (-3, -1)
#guard (BitVec.sdiv (7 : BitVec 8) (-2), BitVec.srem (7 : BitVec 8) (-2)) == (-3, 1)

/-! Tests of each rule at `i1`, `i7`, `i8`, `i33`, `i64` and `i128`, with the
boundary values `0`, `1`, all ones (`-1`), the signed minimum and the
signed maximum. -/

-- `sdiv` at `i8`: it rounds towards zero.
#guard sdivWith false (.value (7 : BitVec 8)) (.value 2) == .ok (.value 3)
#guard sdivWith false (.value (-7 : BitVec 8)) (.value 2) == .ok (.value (-3))
#guard sdivWith false (.value (7 : BitVec 8)) (.value (-2)) == .ok (.value (-3))
#guard sdivWith false (.value (-7 : BitVec 8)) (.value (-2)) == .ok (.value 3)
#guard sdivWith false (.value (127 : BitVec 8)) (.value (-1)) == .ok (.value (-127))
#guard sdivWith false (.value (-128 : BitVec 8)) (.value 1) == .ok (.value (-128))
#guard sdivWith false (.value (-128 : BitVec 8)) (.value (-128)) == .ok (.value 1)
#guard sdivWith false (.value (0 : BitVec 8)) (.value (-1)) == .ok (.value 0)
-- Its UB, each with its reason, and a poison dividend.
#guard sdivWith false (.value (-128 : BitVec 8)) (.value (-1)) ==
  .ub "sdiv of the signed minimum by -1"
#guard sdivWith false (.poison : PoisonOr (BitVec 8)) (.value (-1)) == .ub "sdiv of poison by -1"
#guard sdivWith false (.value (5 : BitVec 8)) (.value 0) == .ub "sdiv by zero"
#guard sdivWith false (.poison : PoisonOr (BitVec 8)) (.value 0) == .ub "sdiv by zero"
#guard sdivWith false (.value (5 : BitVec 8)) .poison == .ub "sdiv by poison"
#guard sdivWith (w := 8) false .poison .poison == .ub "sdiv by poison"
#guard sdivWith false (.poison : PoisonOr (BitVec 8)) (.value 1) == .ok .poison
#guard sdivWith false (.poison : PoisonOr (BitVec 8)) (.value 127) == .ok .poison
-- `exact` at `i8`: a remainder gives poison, and UB comes first.
#guard sdivWith true (.value (-6 : BitVec 8)) (.value 3) == .ok (.value (-2))
#guard sdivWith true (.value (7 : BitVec 8)) (.value 2) == .ok .poison
#guard sdivWith true (.value (-7 : BitVec 8)) (.value (-2)) == .ok .poison
#guard sdivWith true (.value (-128 : BitVec 8)) (.value 2) == .ok (.value (-64))
#guard sdivWith true (.value (-128 : BitVec 8)) (.value (-1)) ==
  .ub "sdiv of the signed minimum by -1"
#guard sdivWith true (.poison : PoisonOr (BitVec 8)) (.value (-1)) == .ub "sdiv of poison by -1"
#guard sdivWith true (.poison : PoisonOr (BitVec 8)) (.value 3) == .ok .poison
#guard sdivWith true (.value (6 : BitVec 8)) (.value 0) == .ub "sdiv by zero"
#guard sdivWith true (.value (6 : BitVec 8)) .poison == .ub "sdiv by poison"

-- `udiv` at `i8`: all ones is 255, and has no `-1` case.
#guard udivWith false (.value (-1 : BitVec 8)) (.value 2) == .ok (.value 127)
#guard udivWith false (.value (-1 : BitVec 8)) (.value (-1)) == .ok (.value 1)
#guard udivWith false (.value (-128 : BitVec 8)) (.value (-1)) == .ok (.value 0)
#guard udivWith false (.value (127 : BitVec 8)) (.value (-128)) == .ok (.value 0)
#guard udivWith false (.value (-128 : BitVec 8)) (.value 1) == .ok (.value (-128))
#guard udivWith false (.poison : PoisonOr (BitVec 8)) (.value (-1)) == .ok .poison
#guard udivWith false (.poison : PoisonOr (BitVec 8)) (.value 1) == .ok .poison
#guard udivWith false (.value (5 : BitVec 8)) (.value 0) == .ub "udiv by zero"
#guard udivWith false (.poison : PoisonOr (BitVec 8)) (.value 0) == .ub "udiv by zero"
#guard udivWith false (.value (5 : BitVec 8)) .poison == .ub "udiv by poison"
#guard udivWith true (.value (-2 : BitVec 8)) (.value 2) == .ok (.value 127)
#guard udivWith true (.value (-2 : BitVec 8)) (.value (-1)) == .ok .poison
#guard udivWith true (.value (-1 : BitVec 8)) (.value (-1)) == .ok (.value 1)
#guard udivWith true (.poison : PoisonOr (BitVec 8)) (.value (-1)) == .ok .poison
#guard udivWith true (.value (5 : BitVec 8)) (.value 0) == .ub "udiv by zero"
#guard udivWith (w := 8) true .poison .poison == .ub "udiv by poison"

-- `srem` at `i8`: the sign of the dividend.
#guard sremValues (.value (7 : BitVec 8)) (.value 2) == .ok (.value 1)
#guard sremValues (.value (-7 : BitVec 8)) (.value 2) == .ok (.value (-1))
#guard sremValues (.value (7 : BitVec 8)) (.value (-2)) == .ok (.value 1)
#guard sremValues (.value (-7 : BitVec 8)) (.value (-2)) == .ok (.value (-1))
#guard sremValues (.value (-128 : BitVec 8)) (.value 3) == .ok (.value (-2))
#guard sremValues (.value (127 : BitVec 8)) (.value (-1)) == .ok (.value 0)
#guard sremValues (.value (-128 : BitVec 8)) (.value (-1)) == .ub "srem of the signed minimum by -1"
#guard sremValues (.poison : PoisonOr (BitVec 8)) (.value (-1)) == .ub "srem of poison by -1"
#guard sremValues (.value (5 : BitVec 8)) (.value 0) == .ub "srem by zero"
#guard sremValues (.value (5 : BitVec 8)) .poison == .ub "srem by poison"
#guard sremValues (.poison : PoisonOr (BitVec 8)) (.value 2) == .ok .poison

-- `urem` at `i8`.
#guard uremValues (.value (-1 : BitVec 8)) (.value 2) == .ok (.value 1)
#guard uremValues (.value (-1 : BitVec 8)) (.value (-1)) == .ok (.value 0)
#guard uremValues (.value (-128 : BitVec 8)) (.value (-1)) == .ok (.value (-128))
#guard uremValues (.value (127 : BitVec 8)) (.value (-128)) == .ok (.value 127)
#guard uremValues (.poison : PoisonOr (BitVec 8)) (.value (-1)) == .ok .poison
#guard uremValues (.value (5 : BitVec 8)) (.value 0) == .ub "urem by zero"
#guard uremValues (.poison : PoisonOr (BitVec 8)) (.value 0) == .ub "urem by zero"
#guard uremValues (.value (5 : BitVec 8)) .poison == .ub "urem by poison"

-- At `i1`, `true` is `-1`, the signed minimum and all ones.
#guard sdivWith false (.value (1 : BitVec 1)) (.value 1) == .ub "sdiv of the signed minimum by -1"
#guard sdivWith true (.value (1 : BitVec 1)) (.value 1) == .ub "sdiv of the signed minimum by -1"
#guard sdivWith false (.value (0 : BitVec 1)) (.value 1) == .ok (.value 0)
#guard sdivWith true (.value (0 : BitVec 1)) (.value 1) == .ok (.value 0)
#guard sdivWith false (.poison : PoisonOr (BitVec 1)) (.value 1) == .ub "sdiv of poison by -1"
#guard sdivWith false (.value (1 : BitVec 1)) (.value 0) == .ub "sdiv by zero"
#guard sremValues (.value (1 : BitVec 1)) (.value 1) == .ub "srem of the signed minimum by -1"
#guard sremValues (.value (0 : BitVec 1)) (.value 1) == .ok (.value 0)
#guard sremValues (.poison : PoisonOr (BitVec 1)) (.value 1) == .ub "srem of poison by -1"
#guard udivWith false (.value (1 : BitVec 1)) (.value 1) == .ok (.value 1)
#guard udivWith true (.value (0 : BitVec 1)) (.value 1) == .ok (.value 0)
#guard udivWith false (.poison : PoisonOr (BitVec 1)) (.value 1) == .ok .poison
#guard udivWith false (.value (1 : BitVec 1)) (.value 0) == .ub "udiv by zero"
#guard uremValues (.value (1 : BitVec 1)) (.value 1) == .ok (.value 0)
#guard uremValues (.poison : PoisonOr (BitVec 1)) (.value 1) == .ok .poison
#guard uremValues (w := 1) (.value 1) .poison == .ub "urem by poison"

-- At `i7`, whose signed range is `-64` to `63`.
#guard sdivWith false (.value (-64 : BitVec 7)) (.value (-1)) ==
  .ub "sdiv of the signed minimum by -1"
#guard sdivWith false (.value (63 : BitVec 7)) (.value (-1)) == .ok (.value (-63))
#guard sdivWith true (.value (-64 : BitVec 7)) (.value 2) == .ok (.value (-32))
#guard sdivWith true (.value (63 : BitVec 7)) (.value 2) == .ok .poison
#guard udivWith false (.value (-64 : BitVec 7)) (.value (-1)) == .ok (.value 0)
#guard udivWith true (.value (-2 : BitVec 7)) (.value 63) == .ok (.value 2)
#guard udivWith true (.value (-1 : BitVec 7)) (.value 63) == .ok .poison
#guard sremValues (.value (-64 : BitVec 7)) (.value (-1)) == .ub "srem of the signed minimum by -1"
#guard sremValues (.value (-64 : BitVec 7)) (.value 63) == .ok (.value (-1))
#guard uremValues (.value (-64 : BitVec 7)) (.value 63) == .ok (.value 1)
#guard uremValues (.poison : PoisonOr (BitVec 7)) (.value (-1)) == .ok .poison

-- At `i33`, whose signed range is `-2^32` to `2^32 - 1`.
#guard sdivWith false (.value (BitVec.intMin 33)) (.value (-1)) ==
  .ub "sdiv of the signed minimum by -1"
#guard sdivWith false (.value (BitVec.intMax 33)) (.value (-1)) ==
  .ok (.value (BitVec.intMin 33 + 1))
#guard sdivWith true (.value (BitVec.intMin 33)) (.value (BitVec.intMin 33)) == .ok (.value 1)
#guard sdivWith true (.value (BitVec.intMax 33)) (.value 2) == .ok .poison
#guard udivWith false (.value (BitVec.intMin 33)) (.value 2) ==
  .ok (.value (BitVec.ofNat 33 (2 ^ 31)))
#guard udivWith true (.value (BitVec.intMax 33)) (.value (-1)) == .ok .poison
#guard sremValues (.value (BitVec.intMin 33)) (.value (BitVec.intMax 33)) == .ok (.value (-1))
#guard uremValues (.value (-1 : BitVec 33)) (.value (BitVec.intMin 33)) ==
  .ok (.value (BitVec.intMax 33))
#guard sremValues (.poison : PoisonOr (BitVec 33)) (.value (-1)) == .ub "srem of poison by -1"
#guard udivWith false (.value (1 : BitVec 33)) (.value 0) == .ub "udiv by zero"

-- At `i64`, the signed minimum and maximum.
#guard sdivWith false (.value (BitVec.intMin 64)) (.value (-1)) ==
  .ub "sdiv of the signed minimum by -1"
#guard sdivWith false (.value (BitVec.intMin 64)) (.value 1) == .ok (.value (BitVec.intMin 64))
#guard sdivWith false (.value (-1 : BitVec 64)) (.value (BitVec.intMin 64)) == .ok (.value 0)
#guard sdivWith true (.value (BitVec.intMax 64)) (.value (BitVec.intMax 64)) == .ok (.value 1)
#guard sdivWith true (.value (BitVec.intMin 64)) (.value (BitVec.intMax 64)) == .ok .poison
#guard udivWith false (.value (-1 : BitVec 64)) (.value (BitVec.intMin 64)) == .ok (.value 1)
#guard udivWith true (.value (BitVec.intMin 64)) (.value (BitVec.intMin 64)) == .ok (.value 1)
#guard sremValues (.value (BitVec.intMin 64)) (.value (-1)) ==
  .ub "srem of the signed minimum by -1"
#guard sremValues (.value (BitVec.intMin 64)) (.value (BitVec.intMax 64)) == .ok (.value (-1))
#guard uremValues (.value (BitVec.intMin 64)) (.value (BitVec.intMax 64)) == .ok (.value 1)
#guard uremValues (.poison : PoisonOr (BitVec 64)) (.value (-1)) == .ok .poison
#guard sdivWith (w := 64) true .poison (.value 0) == .ub "sdiv by zero"

-- At `i128`.
#guard sdivWith false (.value (BitVec.intMin 128)) (.value (-1)) ==
  .ub "sdiv of the signed minimum by -1"
#guard sdivWith false (.value (BitVec.intMax 128)) (.value (-1)) ==
  .ok (.value (BitVec.intMin 128 + 1))
#guard sdivWith true (.value (BitVec.intMin 128)) (.value 2) ==
  .ok (.value (BitVec.ofInt 128 (-2 ^ 126)))
#guard udivWith false (.value (-1 : BitVec 128)) (.value (-1)) == .ok (.value 1)
#guard udivWith true (.value (-1 : BitVec 128)) (.value 2) == .ok .poison
#guard sremValues (.value (BitVec.intMin 128)) (.value 3) == .ok (.value (-2))
#guard uremValues (.value (-1 : BitVec 128)) (.value 3) == .ok (.value 0)
#guard uremValues (.poison : PoisonOr (BitVec 128)) (.value 0) == .ub "urem by zero"
#guard sremValues (.poison : PoisonOr (BitVec 128)) (.value (-1)) == .ub "srem of poison by -1"

end Fir.Core
