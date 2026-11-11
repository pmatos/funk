import FirTest.MemoryRuns

/-!
Tests of refinement with memory. Refinement of memories lets a poison unit
be refined by any unit, and nothing else changes: the same allocations,
frames and other units. The alloc dialect of the tests of runs with memory
allocates, so it lifts no semantics in the set monad; it is lawful in its
monotonicity by its semantics with memory alone, and its runs with memory
refine themselves on refined arguments and from refined memories.
-/

namespace FirTest.MemoryRefine

open Fir Fir.Memory FirTest FirTest.MemoryRuns

/-! # Refining units and memories -/

/-- A poison unit is refined by any unit, and a unit of bits only by
itself. -/
example (b : BitVec 8) : (MemUnit.poison : MemUnit 8) ⊑ MemUnit.bits b := trivial
example (b : BitVec 8) : ¬ ((MemUnit.bits b : MemUnit 8) ⊑ (MemUnit.poison : MemUnit 8)) :=
  fun h => nomatch h
example (b c : BitVec 8) (h : b ≠ c) : ¬ ((MemUnit.bits b : MemUnit 8) ⊑ MemUnit.bits c) :=
  fun h' => h (MemUnit.bits.inj h').symm

/-- A fragment of a pointer is refined only by itself, so a pointer copied
unit by unit keeps its provenance. -/
example (p : Pointer) (i : Nat) : ¬ ((MemUnit.frag p i : MemUnit 8) ⊑ (MemUnit.poison : MemUnit 8)) :=
  fun h => nomatch h

/-- A fresh allocation holds poison, so a store into it gives memories that
refine it. -/
example : let M : Memory 8 := (Memory.empty.alloc .stack 1).2
    ∀ M' : Memory 8, M.store ⟨some 0, 0⟩ [.bits 5] = .ok M' → M ⊑ M' := by
  intro M M' h
  cases h
  exact ⟨⟨rfl, ⟨trivial, trivial⟩, rfl⟩, trivial⟩

/-- Two memories whose allocations differ do not refine each other. -/
example : ¬ ((Memory.empty : Memory 8) ⊑ ((Memory.empty.alloc .heap 1).2 : Memory 8)) :=
  fun h => nomatch h

/-! # The alloc dialect is lawful in its monotonicity -/

/-- Allocating in memories that refine others gives the same pointer, and
memories that refine the others'. -/
theorem alloc_refines {N : Type} [DecidableEq N] {unit : N → Nat} (x : N) (k : AllocKind)
    (n : Nat) : StateRefinedBy Eq (MonadMemory.alloc (m := StateT (Memories N unit) SetM) x k n)
      (MonadMemory.alloc x k n) := by
  intro S S' hS e he
  cases he
  obtain ⟨hp, hm⟩ := hS.alloc x k n
  exact ⟨.ok (S.alloc x k n), rfl, hp, hm⟩

/-- Each alloc op is monotone with memory, wherever a run names the
dialect's memory: `alloc` allocates the same unit from memories that refine
others, and `ret` returns from them. -/
theorem alloc_memMonotone : ∀ op : AllocOp, MemMonotone (d := AllocDialect) op
  | .alloc => fun _ ρ _ _ _ =>
    ⟨fun _ => StateRefinedBy.map _ (fun _ => trivial) (alloc_refines (ρ ()) .stack 1),
      fun h => (nomatch h)⟩
  | .ret => fun _ _ _ _ _ =>
    ⟨fun h => (nomatch h), fun _ S S' hS e he => by
      cases he
      exact ⟨.ok (.ret, S), rfl, rfl, hS⟩⟩

/-- The alloc dialect is lawful in its monotonicity, with no semantics in
the set monad. -/
instance : LawfulDialectMonotone AllocDialect := ⟨fun op _ _ => alloc_memMonotone op⟩

/-- The runs with memory of a valid module of the alloc dialect, whose op
allocates, refine themselves on arguments that refine others. -/
example {f : Func AllocDialect} (hf : f ∈ allocModule.funcs)
    {a a' : HVector toType (f.params.map (·.2))} (ha : a.Forall₂ TyRefinement.IsRefinedBy a') :
    observable (f.memRuns (fun _ : Unit => 8) id allocModule a) ⊑
      observable (f.memRuns (fun _ : Unit => 8) id allocModule a') :=
  Func.memRuns_args_isRefinedBy_of_lawful _ _ allocModule_valid.funcs hf ha

/-- From memories that refine others, a run of a function of the module,
the memories it ends with included, refines its run from those others. -/
example {f : Func AllocDialect} (hf : f ∈ allocModule.funcs)
    {a a' : HVector toType (f.params.map (·.2))} (ha : a.Forall₂ TyRefinement.IsRefinedBy a')
    {S S' : Memories Unit fun _ => 8} (hS : S ⊑ S') :
    letI := DialectMemDenote.denoteAt (d := AllocDialect) (fun _ : Unit => 8) id
    observable (f.memRunsFrom allocModule (a, S)) ⊑ observable (f.memRunsFrom allocModule (a', S')) :=
  Func.memRunsFrom_args_isRefinedBy_of_lawful _ _ allocModule_valid.funcs hf ha hS

/-- The core dialect is lawful in its monotonicity. -/
example : LawfulDialectMonotone CoreDialect := inferInstance

/-- info: 'Fir.Func.memRunsFrom_isRefinedBy_of_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.memRunsFrom_isRefinedBy_of_calls

/-- info: 'Fir.Func.memRunsFrom_replaceBody_isRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.memRunsFrom_replaceBody_isRefinedBy

end FirTest.MemoryRefine
