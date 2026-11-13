import Fir.Core.Values
import Fir.Core.Ops

/-!
# The fast-math flags

A float op may carry the fast-math flags `nnan`, `ninf` and `nsz`
(ADR-2026-11-09-1549). Each is a promise, and the rules read it as LLVM
does:

* `nnan`: no operand and no result is a NaN. A NaN operand, or a result
  that the model computes as a NaN, makes the result poison, and the op
  chooses no NaN.
* `ninf`: no operand and no result is an infinity. An infinite operand, or
  a result that is an infinity, makes the result poison. The result is
  judged after rounding, so a finite result that overflows to an infinity
  breaks the promise too.
* `nsz`: the sign of a zero result does not matter. When the result is a
  zero, the op chooses one bit and flips the zero's sign by it, so `+0`
  and `-0` are both results. Operands are read as they are.

The flags are fir's own: Lean's float model has no poison and no flags.
Whether an operand or a result is a NaN, an infinity or a zero is the
model's reading of its bits, `UnpackedFloat.unpack`.

`contract` and `reassoc` are reserved words that validation rejects, left
to M2's optimizer; these rules ignore them.

A flag only adds results: poison, which every value refines, and a zero of
the other sign. So an op without a flag refines the op with it, and native
code, which ignores the flags, refines the flagged op (the section on
dropping fast-math flags proves both).
-/

namespace Fir.Core

open Float.Model

/-- Whether the flags `a` are among the flags `b`: `nnan`, `ninf` and `nsz`
each set in `b` when set in `a`. The reserved words do not count. -/
structure FastMath.Le (a b : FastMath) : Prop where
  nnan : a.nnan = true → b.nnan = true
  ninf : a.ninf = true → b.ninf = true
  nsz : a.nsz = true → b.nsz = true

/-- Whether the flags may make a result poison: `nnan` or `ninf` is set. -/
def FastMath.mayPoison (fl : FastMath) : Bool := fl.nnan || fl.ninf

/-- Whether the model reads a float as a zero of either sign. -/
def isZeroFloat : UnpackedFloat → Bool
  | .zero _ => true
  | _ => false

/-- Whether the flags make a float poison as an operand or a result: a NaN
under `nnan`, or an infinity under `ninf`. -/
def FastMath.breaks (fl : FastMath) (u : UnpackedFloat) : Bool :=
  fl.nnan && u.isNaN || fl.ninf && u.isInf

/-- Whether an operand among `as`, bits of `float<e,m>`, breaks the flags.
A format that the model does not have breaks none. -/
def operandsBreak (fl : FastMath) (e m : Nat) (as : List (BitVec (floatWidth e m))) : Bool :=
  if h : 2 ≤ e ∧ 0 < m then
    let f : Format :=
      { exponentBits := e, mantissaBitsWithoutImplicit := m, he := h.1, hm := h.2 }
    as.any fun a => fl.breaks (UnpackedFloat.unpack f a)
  else false

/-- `b` with its sign flipped when the bit `c` is set. -/
def flipSign (e m : Nat) (c : BitVec 1) (b : BitVec (floatWidth e m)) :
    BitVec (floatWidth e m) :=
  b ^^^ .ofNat _ (c.toNat * 2 ^ (e + m))

/-- `b` with either sign: the rule chooses one bit and flips the sign by
it. -/
def anySign {μ : Type → Type} [Monad μ] [MonadChoice μ] (e m : Nat)
    (b : BitVec (floatWidth e m)) : μ (PoisonOr (BitVec (floatWidth e m))) := do
  let c ← MonadChoice.choose 1
  pure (.value (flipSign e m c b))

/-- The result `b` of a float op that is not a NaN, which the model reads
as `u`, under the flags: poison for an infinity under `ninf`, either sign
of a zero under `nsz`, and `b` itself otherwise. -/
def flagResult {μ : Type → Type} [Monad μ] [MonadChoice μ] (fl : FastMath) (e m : Nat)
    (b : BitVec (floatWidth e m)) (u : UnpackedFloat) : μ (PoisonOr (BitVec (floatWidth e m))) :=
  if fl.ninf && u.isInf then pure .poison
  else if fl.nsz && isZeroFloat u then anySign e m b
  else pure (.value b)

/-- No operand breaks the flags when there is none. -/
@[simp] theorem operandsBreak_nil (fl : FastMath) (e m : Nat) : operandsBreak fl e m [] = false := by
  unfold operandsBreak
  split <;> rfl

/-! # Tests -/

-- Flipping by `0` keeps the bits; by `1` it flips the sign of `+0` at
-- `f32` and of `-0` at `f16`.
#guard flipSign 8 23 0 0 == 0 && flipSign 8 23 1 0 == 0x80000000
#guard flipSign 5 10 1 0x8000 == 0
-- At `f32`: a NaN breaks `nnan` and not `ninf`, an infinity the other way
-- round, and `1.0` neither.
#guard operandsBreak { nnan := true } 8 23 [0x3f800000, 0x7fc00000] &&
  !operandsBreak { ninf := true } 8 23 [0x3f800000, 0x7fc00000]
#guard operandsBreak { ninf := true } 8 23 [0xff800000] &&
  !operandsBreak { nnan := true } 8 23 [0xff800000]
#guard !operandsBreak { nnan := true, ninf := true, nsz := true } 8 23 [0x3f800000, 0x80000000]
-- A format the model does not have breaks nothing.
#guard !operandsBreak { nnan := true, ninf := true } 1 1 [7]

end Fir.Core
