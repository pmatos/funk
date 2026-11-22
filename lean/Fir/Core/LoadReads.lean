import Fir.Core.EffectLaws

/-!
# A load declared without a read

The effects obligation rejects a declaration of `load` that leaves out the
read of its memory (the human's ruling of 2026-11-10 on #231). The
declaration below gives every core op its set, but `load` only may-UB and
may produce poison. Over the core's own semantics with memory, a `load` of
an `i8` gives the value its unit holds: from a memory whose one allocation
holds `0`, it gives `0`, and from the same memory with that allocation
holding `1`, it gives `1`. Replacing the memory changed what it gave, so it
reads that memory, and the obligation on an op that declares no read of a
memory rejects the declaration.
-/

namespace Fir.Core.Unlawful

open Memory

/-- The core ops' effects, but `load` declared without a read of its
memory. -/
@[instance_reducible] def loadNoRead : DialectEffects CoreDialect where
  Mem := Core.Mem
  poisonClass := Core.Op.poisonClass
  effects
    | .load .. => { mayUB := true, mayPoison := true }
    | op => Core.Op.effects op
  numbered := some

/-- A `load` of an `i8` through a pointer of memory 0 is a valid op
instance. -/
theorem load_typesValid : TypesValid (d := CoreDialect) (.load .nonatomic 8 none 0) := by
  unfold TypesValid; decide

/-- Memories of 8-bit units whose memory holds one live allocation of one
unit, aligned to 1, that holds `b`. -/
def oneUnit (b : BitVec 8) : Memories Unit (unitsOf fun _ : Unit => MemLayout.default) :=
  Memories.empty.set () ⟨[⟨.heap, 1, [.bits b], true, none, false⟩]⟩

/-- An `i8` takes one unit of the default memory, aligned to 1. -/
theorem loadShape_i8 : loadShape MemLayout.default 8 none = (1, 1) := by
  decide +kernel

/-- A load of an `i8` from the allocation of `oneUnit 0` gives `0`. -/
theorem oneUnit_load₀ :
    (oneUnit 0).load () ⟨some 0, 0⟩ (loadShape MemLayout.default 8 none).1
      (loadShape MemLayout.default 8 none).2 = .ok [.bits 0] := by
  rw [loadShape_i8]
  rfl

/-- A load of an `i8` from the allocation of `oneUnit 1` gives `1`. -/
theorem oneUnit_load₁ :
    (oneUnit 1).load () ⟨some 0, 0⟩ (loadShape MemLayout.default 8 none).1
      (loadShape MemLayout.default 8 none).2 = .ok [.bits 1] := by
  rw [loadShape_i8]
  rfl

/-- A load that the declaration leaves without a read of memory 0 reads it,
so the obligations reject the declaration, over the core's own semantics
with memory. -/
theorem loadNoRead_unlawful :
    ¬ @LawfulDialectEffects CoreDialect _ _ _ loadNoRead _ _
      (@DialectMemDenote.mk CoreDialect _ _ loadNoRead fun lay ρ L => Core.memDenoteAt lay ρ L) := by
  intro h
  have hr := @LawfulDialectEffects.readsNot CoreDialect _ _ _ loadNoRead _ _ _ h
    (.load .nonatomic 8 none 0) load_typesValid (.inr rfl) Unit _ (fun _ => MemLayout.default)
    (fun _ => ()) RunItems.empty () (fun h => nomatch h)
  have hc := (hr (.cons (.value ⟨some 0, 0⟩) .nil)).1 rfl
  have h0 := (SetM.stateMap_apply (loadResult MemLayout.default 8)
    (loadAccess 8 none 0 (fun _ : Unit => MemLayout.default) (fun _ => ()) ⟨some 0, 0⟩)
    (oneUnit 0) _).2 (.inl ⟨_, _, (Fir.load_apply _ _ _ _ _ _).2 (.inl ⟨_, oneUnit_load₀, rfl⟩),
      rfl⟩)
  obtain ⟨e', he', hm⟩ := hc (oneUnit 0) ⟨[⟨.heap, 1, [.bits 1], true, none, false⟩]⟩ rfl _ h0
  have hs : (oneUnit 0).set () ⟨[⟨.heap, 1, [.bits 1], true, none, false⟩]⟩ = oneUnit 1 := rfl
  rw [hs] at he'
  rcases (SetM.stateMap_apply _ _ _ _).1 he' with ⟨us, S', hl, rfl⟩ | ⟨_, hl, rfl⟩
  · rcases (Fir.load_apply _ _ _ _ _ _).1 hl with ⟨us', hu, he⟩ | ⟨_, hu, _⟩
    · cases he
      have hu' := hu.symm.trans (oneUnit_load₁)
      cases hu'
      have h1 := congrArg (fun v : HVector toType [Ty.int 8] => match v with | .cons x _ => x) hm.1
      simp [loadResult, decodeInt, unitsFor, unitsValue, ByteOrder.place, MemLayout.default] at h1
      have h2 : (PoisonOr.value 0#8 : PoisonOr (BitVec 8)) = .value 1#8 := h1
      exact absurd (PoisonOr.value.inj h2) (by decide)
    · exact absurd (hu.symm.trans (oneUnit_load₁)) (by simp)
  · rcases (Fir.load_apply _ _ _ _ _ _).1 hl with ⟨_, hu, he⟩ | ⟨_, hu, _⟩
    · cases he
    · exact absurd (hu.symm.trans (oneUnit_load₁)) (by simp)

end Fir.Core.Unlawful
