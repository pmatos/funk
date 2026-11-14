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
example (m : Nat) (p : Pointer) (i : Nat) : ¬ ((MemUnit.frag m p i : MemUnit 8) ⊑ (MemUnit.poison : MemUnit 8)) :=
  fun h => nomatch h

/-- A fresh allocation holds poison, so a store into it gives memories that
refine it. -/
example : let M : Memory 8 := (Memory.empty.alloc .stack 1 1).2
    ∀ M' : Memory 8, M.store ⟨some 0, 0⟩ [.bits 5] = .ok M' → M ⊑ M' := by
  intro M M' h
  cases h
  exact ⟨⟨rfl, rfl, rfl, rfl, fun _ => ⟨trivial, trivial⟩⟩, trivial⟩

/-- No access reaches a freed block, so its units are not compared: a store
to a stack slot that is then freed may be dropped. -/
example : let M : Memory 8 := (Memory.empty.alloc .stack 1 1).2
    ∀ N : Memory 8, M.store ⟨some 0, 0⟩ [.bits 5] = .ok N → N.free 0 ⊑ M.free 0 := by
  intro M N h
  cases h
  exact ⟨⟨rfl, rfl, rfl, rfl, fun h => Bool.noConfusion h⟩, trivial⟩

/-- While the block is live, the store may not be dropped. -/
example : let M : Memory 8 := (Memory.empty.alloc .stack 1 1).2
    ∀ N : Memory 8, M.store ⟨some 0, 0⟩ [.bits 5] = .ok N → ¬ (N ⊑ M) := by
  intro M N h hr
  cases h
  exact nomatch (hr.1.2.2.2.2 rfl).1

/-- Two memories whose allocations differ do not refine each other. -/
example : ¬ ((Memory.empty : Memory 8) ⊑ ((Memory.empty.alloc .heap 1 1).2 : Memory 8)) :=
  fun h => nomatch h

/-- Nor do two memories whose allocations differ only in their alignment,
in either direction, so an access is aligned in both or in neither. -/
example : ¬ (((Memory.empty.alloc .stack 1 2).2 : Memory 8) ⊑
    ((Memory.empty.alloc .stack 1 8).2 : Memory 8)) :=
  fun h => absurd h.1.2.1 (by decide)
example : ¬ (((Memory.empty.alloc .stack 1 8).2 : Memory 8) ⊑
    ((Memory.empty.alloc .stack 1 2).2 : Memory 8)) :=
  fun h => absurd h.1.2.1 (by decide)

/-! # The alloc dialect is lawful in its monotonicity -/

/-- Allocating in memories that refine others gives the same pointer, and
memories that refine the others'. -/
theorem alloc_refines {N : Type} [DecidableEq N] {unit : N → Nat} (x : N) (k : AllocKind)
    (n al : Nat) :
    StateRefinedBy Eq (MonadMemory.alloc (m := StateT (Memories N unit) SetM) x k n al)
      (MonadMemory.alloc x k n al) := by
  intro S S' hS e he
  cases he
  obtain ⟨hp, hm⟩ := hS.alloc x k n al
  exact ⟨.ok (S.alloc x k n al), rfl, hp, hm⟩

/-- Each alloc op is monotone with memory, wherever a run names the
dialect's memory: `alloc` allocates the same unit from memories that refine
others, and `ret` returns from them. -/
theorem alloc_memMonotone : ∀ op : AllocOp, MemMonotone (d := AllocDialect) op
  | .alloc => fun _ ρ _ _ _ =>
    ⟨fun _ => StateRefinedBy.map _ (fun _ => trivial) (alloc_refines (ρ ()) .stack 1 1),
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
    observable (f.memRuns (fun _ : Unit => MemLayout.default) id allocModule a) ⊑
      observable (f.memRuns (fun _ : Unit => MemLayout.default) id allocModule a') :=
  Func.memRuns_args_isRefinedBy_of_lawful _ _ allocModule_valid.funcs hf ha

/-- From memories that refine others, a run of a function of the module,
the memories it ends with included, refines its run from those others. -/
example {f : Func AllocDialect} (hf : f ∈ allocModule.funcs)
    {a a' : HVector toType (f.params.map (·.2))} (ha : a.Forall₂ TyRefinement.IsRefinedBy a')
    {S S' : Memories Unit (unitsOf fun _ : Unit => MemLayout.default)} (hS : S ⊑ S') :
    letI := DialectMemDenote.denoteAt (d := AllocDialect) (fun _ : Unit => MemLayout.default) id
    observable (f.memRunsFrom allocModule (a, S)) ⊑ observable (f.memRunsFrom allocModule (a', S')) :=
  Func.memRunsFrom_args_isRefinedBy_of_lawful _ _ allocModule_valid.funcs hf ha hS

/-! # Congruence in the callee, with memory, applies -/

/-- A body with no blocks: a function with it never starts. -/
def noBlocks : Region AllocDialect := { blocks := [] }

/-- `allocMain` with no blocks, in its module so changed, has no path that
returns, hits UB or runs out of fuel, from any memories: each is stuck. -/
theorem noBlocks_outcomes (a : HVector toType (allocMain.params.map (·.2)))
    (S : Memories Unit (unitsOf fun _ : Unit => MemLayout.default)) (m : Nat)
    (o : Outcome (List (DVal AllocDialect) × Memories Unit (unitsOf fun _ : Unit =>
        MemLayout.default))) :
    letI := DialectMemDenote.denoteAt (d := AllocDialect) (fun _ : Unit => MemLayout.default) id
    ¬ ((allocMain.replaceBody allocMain.name noBlocks).memRunsFrom
      (allocModule.replaceBody allocMain.name noBlocks) (a, S) m).outcomes o := by
  letI := DialectMemDenote.denoteAt (d := AllocDialect) (fun _ : Unit => MemLayout.default) id
  have key : ∀ x, Ev.NotStuck x → ¬ ((allocMain.replaceBody allocMain.name noBlocks).memRunsFrom
      (allocModule.replaceBody allocMain.name noBlocks) (a, S) m) x := by
    intro x hx h
    obtain ⟨p, hp, -⟩ := (Func.memRunsFrom_run hx).1 h
    simp [Func.enter, Func.blocks, noBlocks, stuck] at hp
  cases o with
  | ret _ => exact key _ fun _ h => nomatch h
  | ub _ => exact key _ fun _ h => nomatch h
  | fuelExhausted => exact key _ fun _ h => nomatch h


/-- No budget lets the new `allocMain` run out of fuel. -/
theorem noBlocks_bounded :
    letI := DialectMemDenote.denoteAt (d := AllocDialect) (fun _ : Unit => MemLayout.default) id
    ∃ B, ((allocMain.replaceBody allocMain.name noBlocks).memRunsFrom (Mem := Unit)
      (unit := unitsOf fun _ : Unit => MemLayout.default) (allocModule.replaceBody allocMain.name
          noBlocks)).BoundedBy B :=
  ⟨0, fun ⟨a, S⟩ => .inr fun m _ => noBlocks_outcomes a S m .fuelExhausted⟩

/-- The new `allocMain` refines the old from every memories: it has no
observable behaviour. -/
theorem noBlocks_refines :
    letI := DialectMemDenote.denoteAt (d := AllocDialect) (fun _ : Unit => MemLayout.default) id
    allocMain.memRunsFrom (Mem := Unit) (unit := unitsOf fun _ : Unit => MemLayout.default)
        allocModule ⊑
      (allocMain.replaceBody allocMain.name noBlocks).memRunsFrom (Mem := Unit)
        (unit := unitsOf fun _ : Unit => MemLayout.default) (allocModule.replaceBody
            allocMain.name noBlocks) := by
  intro ⟨a, S⟩ t ht
  cases t with
  | ret o => obtain ⟨n, hn⟩ := ht; exact (noBlocks_outcomes a S n (.ret o) hn).elim
  | ub r => obtain ⟨n, hn⟩ := ht; exact (noBlocks_outcomes a S n (.ub r) hn).elim
  | fuelExhausted => exact (noBlocks_outcomes a S 0 .fuelExhausted (ht 0)).elim

/-- So congruence in the callee, with memory, applies: every function of
the module is refined, with memory, by its counterpart in the module with
the new body. -/

example {f : Func AllocDialect} (hf : f ∈ allocModule.funcs)
    (a : HVector toType (f.params.map (·.2))) :
    observable (f.memRuns (fun _ : Unit => MemLayout.default) id allocModule a) ⊑
      observable ((f.replaceBody allocMain.name noBlocks).memRuns (fun _ : Unit =>
          MemLayout.default) id
        (allocModule.replaceBody allocMain.name noBlocks) a) := by
  have h := Func.memRuns_replaceBody_isRefinedBy_of_bound (fun _ : Unit => MemLayout.default) id
    Core.Ty.isRefinedBy_refl Core.Ty.isRefinedBy_trans allocModule_valid (g := allocMain)
    (by simp [allocModule, Module.funcs]) noBlocks ?hb ?hr hf
  case hb => exact noBlocks_bounded
  case hr => exact noBlocks_refines
  exact h.2 a

/-- The core dialect is lawful in its monotonicity. -/
example : LawfulDialectMonotone CoreDialect := inferInstance

/-- info: 'Fir.Func.memRunsFrom_isRefinedBy_of_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.memRunsFrom_isRefinedBy_of_calls

/-- info: 'Fir.Func.memRunsFrom_replaceBody_isRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Func.memRunsFrom_replaceBody_isRefinedBy

end FirTest.MemoryRefine
