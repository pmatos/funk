import Fir.Core.LoadReads

/-!
# A store declared without a write

The effects obligation rejects a declaration of `store` that leaves out the
write of its memory, as it rejects a `load` declared without a read (the
human's ruling of 2026-11-10 on #231). The declaration below gives every
core op its set, but `store` only may-UB. Over the core's own semantics
with memory, a `store` of the `i8` `1` to a memory whose one allocation
holds `0` ends with that allocation holding `1`. The unit it held before
is gone, so the store writes that memory, and the obligation on an op that
declares no write of a memory rejects the declaration.
-/

namespace Fir.Core.Unlawful

open Memory

/-- The core ops' effects, but `store` declared without a write of its
memory. -/
@[instance_reducible] def storeNoWrite : DialectEffects CoreDialect where
  Mem := Core.Mem
  poisonClass := Core.Op.poisonClass
  effects
    | .store .. => { mayUB := true }
    | op => Core.Op.effects op
  numbered := some

/-- A `store` of an `i8` through a pointer of memory 0 is a valid op
instance. -/
theorem store_typesValid : TypesValid (d := CoreDialect) (.store .nonatomic 8 none 0) := by
  unfold TypesValid; decide

/-- An `i8` is stored to the default memory aligned to 1. -/
theorem storeAlign_i8 : storeAlign MemLayout.default 8 none = 1 := by
  decide +kernel

/-- A store of the `i8` `1` to the allocation of `oneUnit 0` gives
`oneUnit 1`. -/
theorem oneUnit_store :
    (oneUnit 0).store () ⟨some 0, 0⟩ (storeUnits MemLayout.default (.value 1#8))
      (storeAlign MemLayout.default 8 none) = .ok (oneUnit 1) := by
  rw [storeAlign_i8]
  rfl

/-- A store that the declaration leaves without a write of memory 0 writes
it, so the obligations reject the declaration, over the core's own
semantics with memory. -/
theorem storeNoWrite_unlawful :
    ¬ @LawfulDialectEffects CoreDialect _ _ _ storeNoWrite _ _
      (@DialectMemDenote.mk CoreDialect _ _ storeNoWrite fun lay ρ L => Core.memDenoteAt lay ρ L) :=
          by
  intro h
  have hw := @LawfulDialectEffects.writesNot CoreDialect _ _ _ storeNoWrite _ _ _ h
    (.store .nonatomic 8 none 0) store_typesValid (.inr rfl) Unit _ (fun _ => MemLayout.default)
    (fun _ => ()) RunItems.empty () (fun h => nomatch h)
  have hc := (hw (.cons (.value 1#8) (.cons (.value ⟨some 0, 0⟩) .nil))).1 rfl
  have h1 := (SetM.stateMap_apply (fun _ => (.nil : HVector toType ([] : List Ty)))
    (storeAccess 8 none 0 (fun _ : Unit => MemLayout.default) (fun _ => ()) (.value 1#8) ⟨some 0, 0⟩)
    (oneUnit 0) _).2 (.inl ⟨(), oneUnit 1, (Fir.store_apply _ _ _ _ _ _).2
      (.inl ⟨_, oneUnit_store, rfl⟩), rfl⟩)
  exact absurd (hc _ _ _ h1) (by decide)

end Fir.Core.Unlawful
