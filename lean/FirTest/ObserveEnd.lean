import Fir

/-!
Tests of what an observer sees at a return (ADR-2026-11-09-1540, #233): the
returned values and the memory reachable from them and from what escaped,
compared up to a one-to-one renaming of allocations, with a dangling pointer
poison wherever the source has it; and the world's actions on escaped
memory. Each run here has one memory of bytes, and the core's values.
-/

namespace FirTest.ObserveEnd

open Fir Fir.Memory

/-- One memory, of bytes. -/
abbrev w : Unit → Nat := fun _ => 8

/-- The end of a return, with the core's values, the one memory and the
address rule `same`. -/
abbrev E := End w (fun _ => ()) AddrRule.same (List (DVal CoreDialect))

/-- A live stack block of one byte holding `b`. -/
def byte (b : Nat) : Block 8 := ⟨.stack, 1, [.bits (BitVec.ofNat 8 b)], true, none⟩

/-- A live stack block of one unit holding the fragment of a pointer into
`a`. -/
def link (a : AllocId) : Block 8 := ⟨.stack, 1, [.frag 0 ⟨some a, 0⟩ 0], true, none⟩

/-- The memories whose one memory has the blocks `bs`. -/
def mems (bs : List (Block 8)) : Memories Unit w := Memories.empty.set () ⟨bs⟩

/-- A returned pointer into the allocation `a`. -/
def ptr (a : AllocId) : DVal CoreDialect := ⟨.ptr 0, .value ⟨some a, 0⟩⟩

/-- A renaming of the one memory by a list: the allocation `a` is renamed
to the `a`-th element, if there is one. -/
def ren (l : List (Option AllocId)) : Renaming Unit := fun _ a => l[a]?.join

/-! # Memory no observer reaches is not compared -/

/-- A return of nothing does not show memory: a store the target dropped to
an allocation that never escaped is not seen. -/
example : (⟨[], mems [byte 5], []⟩ : E) ⊑ (⟨[], mems [byte 7], []⟩ : E) := by
  refine ⟨ren [], ?_, rfl, fun i e h => by simp at h, fun _ _ h => by simp [HasPtrs.ptrs] at h,
    trivial, fun _ a _ h => ?_⟩
  · intro _ a b c h
    simp [ren] at h
  · simp [ren] at h

/-! # The renaming -/

/-- The target dropped the source's first allocation, so its ids shift by
one: renaming the source's allocation 1 to the target's 0 shows the
returned pointer and the byte it points to. -/
example : (⟨[ptr 1], mems [byte 9, byte 5], []⟩ : E) ⊑ (⟨[ptr 0], mems [byte 5], []⟩ : E) := by
  refine ⟨ren [none, some 0], ?_, rfl, fun i e h => by simp at h, ?_, ?_, ?_⟩
  · intro _ a b c ha hb
    match a, b, ha, hb with
    | 1, 1, _, _ => rfl
    | 0, _, ha, _ | _, 0, _, ha | a + 2, _, ha, _ | _, b + 2, _, ha => simp [ren] at ha
  · intro n p hp
    simp [HasPtrs.ptrs, TyPointers.ptrs, Core.Ty.ptrs, PoisonOr.ptrsOf, ptr] at hp
    obtain ⟨rfl, rfl⟩ := hp
    intro a ha _
    cases ha
    rfl
  · exact ⟨⟨rfl, rfl⟩, trivial⟩
  · intro _ a a' ha
    match a, ha with
    | 1, ha =>
      cases ha
      refine ⟨⟨rfl, rfl, rfl, rfl, rfl, fun _ => ⟨rfl, trivial⟩⟩, fun b hb _ n p hp => ?_⟩
      cases hb
      simp [HasPtrs.ptrs, MemUnit.ptrs, byte] at hp
    | 0, ha | a + 2, ha => simp [ren] at ha

/-- Merging two allocations is not a refinement: a renaming that shows both
returned pointers in one allocation is not one-to-one. -/
example : ¬ (⟨[ptr 0, ptr 1], mems [byte 5, byte 5], []⟩ : E) ⊑
    (⟨[ptr 0, ptr 0], mems [byte 5], []⟩ : E) := by
  rintro ⟨R, hi, -, -, hc, hv, -⟩
  have hcov : ∀ a, a < 2 → ∃ c, R () a = some c := fun a ha =>
    Option.isSome_iff_exists.1 <| hc 0 ⟨some a, 0⟩ (by
      match a, ha with
      | 0, _ | 1, _ => simp [HasPtrs.ptrs, TyPointers.ptrs, Core.Ty.ptrs, PoisonOr.ptrsOf, ptr])
      a rfl (by match a, ha with | 0, _ | 1, _ => rfl)
  obtain ⟨c₀, h₀⟩ := hcov 0 (by decide)
  obtain ⟨c₁, h₁⟩ := hcov 1 (by decide)
  simp [HasPtrs.map, TyPointers.map, Core.Ty.mapPtrs, PoisonOr.mapPtr, Renaming.ptr, ptr,
    Memories.freed, mems, byte, h₀, h₁, HRefinement.IsRefinedBy, List.IsRefinedBy,
    TyRefinement.IsRefinedBy, Core.Ty.IsRefinedBy, PoisonOr.IsRefinedBy] at hv
  obtain ⟨rfl, rfl⟩ := hv
  exact absurd (hi () 0 1 0 h₀ h₁) (by decide)

/-! # Dangling pointers -/

/-- A returned pointer into a freed allocation is poison in the comparison:
the target may return poison in its place. -/
example : (⟨[ptr 0], mems [(byte 5).kill], []⟩ : E) ⊑
    (⟨[⟨.ptr 0, .poison⟩], mems [(byte 5).kill], []⟩ : E) :=
  ⟨ren [], by intro _ a b c h; simp [ren] at h, rfl, fun i e h => by simp at h,
    fun n p hp a ha hf => by
      simp [HasPtrs.ptrs, TyPointers.ptrs, Core.Ty.ptrs, PoisonOr.ptrsOf, ptr] at hp
      obtain ⟨rfl, rfl⟩ := hp
      cases ha
      simp [Memories.freed, mems, byte, Block.kill] at hf,
    ⟨⟨rfl, trivial⟩, trivial⟩,
    fun _ a _ h => by simp [ren] at h⟩

/-! # Memory reached through memory -/

/-- The returned pointer reaches a second allocation through the pointer
stored in the first, so the byte stored there is seen: a target that
stored another byte there does not refine the source. -/
example : ¬ (⟨[ptr 0], mems [link 1, byte 5], []⟩ : E) ⊑
    (⟨[ptr 0], mems [link 1, byte 7], []⟩ : E) := by
  rintro ⟨R, -, -, -, hc, hv, hb⟩
  obtain ⟨c₀, h₀⟩ := Option.isSome_iff_exists.1 <| hc 0 ⟨some 0, 0⟩
    (by simp [HasPtrs.ptrs, TyPointers.ptrs, Core.Ty.ptrs, PoisonOr.ptrsOf, ptr]) 0 rfl rfl
  simp [HasPtrs.map, TyPointers.map, Core.Ty.mapPtrs, PoisonOr.mapPtr, Renaming.ptr, ptr,
    Memories.freed, mems, link, h₀, HRefinement.IsRefinedBy, List.IsRefinedBy,
    TyRefinement.IsRefinedBy, Core.Ty.IsRefinedBy, PoisonOr.IsRefinedBy] at hv
  subst hv
  obtain ⟨-, hc₀⟩ := hb () 0 0 h₀
  obtain ⟨c₁, h₁⟩ := Option.isSome_iff_exists.1 <| hc₀ (link 1) rfl rfl 0 ⟨some 1, 0⟩
    (by simp [HasPtrs.ptrs, MemUnit.ptrs, link]) 1 rfl rfl
  have hs₀ := (hb () 0 0 h₀).1
  simp [Block.OptSeenIn, Block.SeenIn, mems, link, HasPtrs.map, MemUnit.mapPtr, Renaming.ptr,
    Memories.freed, byte, h₁, HRefinement.IsRefinedBy, List.IsRefinedBy,
    MemUnit.IsRefinedBy] at hs₀
  obtain ⟨-, rfl⟩ := hs₀
  have hs₁ := (hb () 1 1 h₁).1
  simp [Block.OptSeenIn, Block.SeenIn, mems, byte, HasPtrs.map, MemUnit.mapPtr,
    HRefinement.IsRefinedBy, List.IsRefinedBy, MemUnit.IsRefinedBy] at hs₁

/-! # What escaped -/

/-- An escaped allocation is seen whether or not a returned pointer reaches
it: a target whose escaped byte differs does not refine the source. -/
example : ¬ (⟨[], mems [byte 5], [((), 0)]⟩ : E) ⊑ (⟨[], mems [byte 7], [((), 0)]⟩ : E) := by
  rintro ⟨R, -, -, he, -, -, hb⟩
  obtain ⟨_, he', -, h₀⟩ := he 0 ((), 0) rfl
  cases he'
  have hs := (hb () 0 0 h₀).1
  simp [Block.OptSeenIn, Block.SeenIn, mems, byte, HasPtrs.map, MemUnit.mapPtr,
    HRefinement.IsRefinedBy, List.IsRefinedBy, MemUnit.IsRefinedBy] at hs

/-- The traced state of a run whose one allocation, a byte holding 5, has
escaped with the handle 0. -/
def escaped5 : TraceState Unit w := ⟨mems [byte 5], [((), 0)]⟩

/-- Letting an allocation escape gives its handle: a new one at the end of
the list, or the one it already has. -/
example : (TraceState.escape (⟨mems [byte 5, byte 6], []⟩ : TraceState Unit w) () 1).1 = some 0 ∧
    (escaped5.escape () 0).1 = some 0 := by decide

/-- An id that the memory has not allocated cannot escape. -/
example : (escaped5.escape () 1).1 = none ∧ (escaped5.escape () 1).2.escaped = [((), 0)] := by
  decide

/-! # The world's actions -/

/-- The blocks of the one memory of a traced state, if there is one. -/
def blocksOf (s : Option (TraceState Unit w)) : Option (List (Block 8)) :=
  s.map fun s => (s.mem.mem ()).blocks

-- The world writes into an escaped allocation, inside it.
example : blocksOf ((WorldAct.store 0 0 [.bits 7]).apply (fun _ => ()) escaped5) =
    some [byte 7] := by decide
-- It writes a pointer into an escaped allocation by its handle.
example : blocksOf ((WorldAct.store 0 0 [.frag 0 (some 0) 0 0]).apply (fun _ => ()) escaped5) =
    some [link 0] := by decide
-- It cannot write outside the allocation, nor into one that did not escape.
example : blocksOf ((WorldAct.store 0 1 [.bits 7]).apply (fun _ => ()) escaped5) = none := by
  decide
example : blocksOf ((WorldAct.store 1 0 [.bits 7]).apply (fun _ => ()) escaped5) = none := by
  decide
-- An allocation it creates is on the heap, aligned to a power of two, and
-- escapes at once, and it may free it; it cannot free a stack allocation.
example : ((WorldAct.alloc 0 4 2).apply (fun _ => ()) escaped5).map (·.escaped) =
    some [((), 0), ((), 1)] := by decide
example : blocksOf (WorldAct.applyAll (fun _ => ()) [.alloc 0 1 0, .free 1] escaped5) =
    some [byte 5, (⟨.heap, 1, [.poison], true, none⟩ : Block 8).kill] := by decide
example : blocksOf ((WorldAct.free 0).apply (fun _ => ()) escaped5) = none := by decide

/-- The world's answer to an event is in the act, with the actions it took,
and the run goes on from the traced state they leave. -/
example : TraceM.ask (E := Nat) (Ans := Nat) (fun _ => ()) 3 escaped5
    (.ok (9, [⟨3, (9, [.store 0 0 [.bits 7]])⟩], ⟨mems [byte 7], [((), 0)]⟩)) :=
  ⟨9, [.store 0 0 [.bits 7]], _, rfl, rfl⟩

end FirTest.ObserveEnd
