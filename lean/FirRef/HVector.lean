import Fir.Execution.Interpreter

/-!
Vectors of values built and read in loops of tail calls
(`docs/decisions/fir-ref-fast-paths.md#wide-values`). The spec's
`HVector.toDVals`, and a vector built by consing each value onto the vector of
the values after it, take stack for each value, so a `ret` of thousands of
values overflowed a 256 KiB stack (#405).

`toDValsFast` is `HVector.toDVals` with an accumulator, and
`toDVals_eq_toDValsFast` makes Lean compile `fir-ref`'s calls of the spec's
function as calls of it. `ofRev` builds the vector of a list of values given
the last first, consing from its end; the proof that the list has the
vector's types is erased.
-/

namespace FirRef

open Fir

variable {Ty : Type} [TyDenote Ty]

/-- `HVector.toDVals vs`, after `acc`, the last first. -/
def toDValsTR : {ts : List Ty} → HVector toType ts → List ((t : Ty) × ⟦t⟧) →
    List ((t : Ty) × ⟦t⟧)
  | [], .nil, acc => acc.reverse
  | t :: _, .cons v vs, acc => toDValsTR vs (⟨t, v⟩ :: acc)

theorem toDValsTR_eq : ∀ {ts : List Ty} (vs : HVector toType ts) (acc : List ((t : Ty) × ⟦t⟧)),
    toDValsTR vs acc = acc.reverse ++ vs.toDVals
  | [], .nil, acc => by simp [toDValsTR, HVector.toDVals]
  | _ :: _, .cons v vs, acc => by simp [toDValsTR, HVector.toDVals, toDValsTR_eq vs]

/-- `HVector.toDVals`, in a loop of tail calls. -/
def toDValsFast {ts : List Ty} (vs : HVector toType ts) : List ((t : Ty) × ⟦t⟧) :=
  toDValsTR vs []

@[csimp] theorem toDVals_eq_toDValsFast : @HVector.toDVals = @toDValsFast := by
  funext Ty _ ts vs
  simp [toDValsFast, toDValsTR_eq]

/-- `vs`, at a list of types equal to its own. -/
@[inline] def recast {us us' : List Ty} (h : us = us') (vs : HVector toType us) :
    HVector toType us' := h ▸ vs

/-- The values of `rev`, the last first, in front of `acc`. -/
def onto : (rev : List ((t : Ty) × ⟦t⟧)) → {us : List Ty} → HVector toType us →
    HVector toType ((rev.map (·.1)).reverse ++ us)
  | [], _, acc => acc
  | ⟨_, v⟩ :: rev, _, acc => recast (by simp) (onto rev (.cons v acc))

/-- The vector of the values of `rev`, the last first, which have the types
`ts`. -/
@[inline] def ofRev (rev : List ((t : Ty) × ⟦t⟧)) {ts : List Ty}
    (h : (rev.map (·.1)).reverse = ts) : HVector toType ts :=
  recast (by simp [h]) (onto rev .nil)

theorem toDVals_recast {us us' : List Ty} (h : us = us') (vs : HVector toType us) :
    (recast h vs).toDVals = vs.toDVals := by
  subst h; rfl

theorem toDVals_onto : ∀ (rev : List ((t : Ty) × ⟦t⟧)) {us : List Ty} (acc : HVector toType us),
    (onto rev acc).toDVals = rev.reverse ++ acc.toDVals
  | [], _, _ => rfl
  | ⟨_, _⟩ :: rev, _, acc => by
    simp [onto, toDVals_recast, toDVals_onto rev, HVector.toDVals]

theorem toDVals_ofRev (rev : List ((t : Ty) × ⟦t⟧)) {ts : List Ty}
    (h : (rev.map (·.1)).reverse = ts) : (ofRev rev h).toDVals = rev.reverse := by
  simp [ofRev, toDVals_recast, toDVals_onto, HVector.toDVals]

/-- A vector is its values. -/
theorem toDVals_inj : ∀ {ts : List Ty} {vs ws : HVector toType ts},
    vs.toDVals = ws.toDVals → vs = ws
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons _ _, .cons _ _, h => by
    simp only [HVector.toDVals, List.cons.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at h
    rw [h.1, toDVals_inj h.2]

end FirRef
