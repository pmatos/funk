import Fir.Core.LoadLaws

/-!
# Pointer load obligations

`loadPtr` touches memory, so it meets each obligation with memory by its
own rule, as `load` does (the section on load obligations), wherever a run
names the core's memories and whatever their layout entries. Its rule is
`load`'s with the units of a pointer of its memory `M` and their decoding
as such a pointer, so each proof is `load`'s with that decoding:

* _Effects._ It may be UB and may give poison, as it declares. It writes no
  unit of any memory, and allocates and frees in none. It reads no memory
  but the memory of its pointer.
* _Totality._ It has an outcome from any memories: UB, or a value.
* _Monotonicity._ A poison pointer is UB, which every outcome refines. On
  the same pointer, from memories that refine others, it faults for the
  same reason or loads units that refine the others', and their decoding
  as a pointer refines the others' (`decodePtr_isRefinedBy`).
* _Poison with memory._ A poison pointer gives no result, and its UB is the
  UB of a pointer with no provenance in its place, from the same memories.
  It gives a result from memories inside a call that hold an allocation of
  its units at its alignment.
* _Finitely many outcomes._ It has at most one that ends, from any
  memories.
-/

namespace Fir.Core

open Memory

variable (o : Memory.Ordering) (mp : Nat) (a : Option Nat) (n : Nat)

section

variable {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : Mem → N)

local notation "SM" => StateT (Memories N (unitsOf lay)) SetM

/-- The load that `loadPtr`'s rule makes through the pointer `p`, in the
state layer over the set monad. -/
abbrev loadPtrAccess (p : Pointer) : SM (List (MemUnit (unitsOf lay (ρ n)))) :=
  MonadMemory.load (ρ n) p (ptrShape lay ρ mp a n).1 (ptrShape lay ρ mp a n).2

/-- `loadPtr` runs with memory by its rule. -/
theorem loadPtr_denote (p : PoisonOr Pointer) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ
    @Eq (SM (HVector toType [Ty.ptr mp]))
      (DialectDenote.denote (d := CoreDialect) (m := SM) (Op.loadPtr o mp a n) (.cons p .nil))
      (loadPtrRule lay ρ mp a n p) :=
  rfl

/-- What `loadPtr` runs by its own rule has a property when its rule has it
on every pointer. -/
theorem loadPtr_ownRuleHas {P : {α : Type} → SM α → Prop}
    (h : ∀ p, P (loadPtrRule lay ρ mp a n p : SM (HVector toType [Ty.ptr mp]))) :
    OwnRuleHas lay ρ P (d := CoreDialect) (.loadPtr o mp a n) := fun
  | .cons p .nil => ⟨fun _ => h p, fun h => nomatch h⟩

/-- `loadPtr` writes no unit of any memory. -/
theorem loadPtr_writesNot (x : N) :
    OwnRuleHas lay ρ (WritesNot x) (d := CoreDialect) (.loadPtr o mp a n) :=
  loadPtr_ownRuleHas o mp a n lay ρ fun
    | .poison => fun _ _ _ h => nomatch h
    | .value p => (Fir.load_writesNot (unit := unitsOf lay) _ p _ _ x).map _

/-- `loadPtr` neither allocates nor frees in any memory. -/
theorem loadPtr_allocatesNot (x : N) :
    OwnRuleHas lay ρ (AllocatesNot x) (d := CoreDialect) (.loadPtr o mp a n) :=
  loadPtr_ownRuleHas o mp a n lay ρ fun
    | .poison => fun _ _ _ h => nomatch h
    | .value p => (Fir.load_allocatesNot (unit := unitsOf lay) _ p _ _ x).map _

/-- `loadPtr` reads no memory but the memory of its pointer. -/
theorem loadPtr_readsNot (x : N)
    (hx : ¬ ((Fir.effects (d := CoreDialect) (.loadPtr o mp a n)).reads.map ρ).Has x) :
    OwnRuleHas lay ρ (ReadsNot x) (d := CoreDialect) (.loadPtr o mp a n) :=
  loadPtr_ownRuleHas o mp a n lay ρ fun
    | .poison => fun _ _ _ e he => by
      subst he
      exact ⟨_, rfl, rfl⟩
    | .value p => (Fir.load_readsNot (unit := unitsOf lay) _ p _ _
        fun h => hx (List.mem_singleton.2 h.symm)).map _

/-- `loadPtr` has an outcome from any memories. -/
theorem loadPtr_memTotal : MemTotal (d := CoreDialect) (.loadPtr o mp a n) := fun lay ρ =>
  loadPtr_ownRuleHas o mp a n lay ρ fun
    | .poison => fun _ => ⟨_, rfl⟩
    | .value p => (Fir.load_hasOutcome (unit := unitsOf lay) _ p _ _).map _

/-- `loadPtr` has at most one outcome that ends, from any memories. -/
theorem loadPtr_finitelyMany
    (args : HVector toType (Fir.sig (d := CoreDialect) (Op.loadPtr o mp a n))) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ
    FinitelyMany (DialectDenote.denote (d := CoreDialect)
      (m := SM) (Op.loadPtr o mp a n) args) := by
  match args with
  | .cons p .nil =>
    show FinitelyMany (loadPtrRule lay ρ mp a n p : SM _)
    cases (p : PoisonOr Pointer) with
    | poison => exact fun _ => ⟨[], fun _ h => nomatch h⟩
    | value q =>
      intro S
      obtain ⟨L, hL⟩ := Fir.load_finitelyMany (unit := unitsOf lay) (ρ n) q
        (ptrShape lay ρ mp a n).1 (ptrShape lay ρ mp a n).2 S
      refine ⟨L.map fun r => (loadPtrResult lay ρ mp n r.1, r.2), fun x hx => ?_⟩
      rcases (SetM.stateMap_apply _ _ S _).1 hx with ⟨us, S', hp, he⟩ | ⟨_, _, he⟩ <;> cases he
      exact List.mem_map.2 ⟨(us, S'), hL _ hp, rfl⟩

end

/-- From memories that refine others, `loadPtr` on a pointer that refines
another faults for the same reason or gives a pointer that refines the
other's; on a poison pointer it is UB, which every outcome refines. -/
theorem loadPtr_memMonotone : MemMonotone (d := CoreDialect) (.loadPtr o mp a n) := by
  intro N _ lay ρ args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons p .nil, .cons p' .nil, ⟨hp, _⟩ =>
    show StateRefinedBy _ (loadPtrRule lay ρ mp a n p) (loadPtrRule lay ρ mp a n p')
    cases p with
    | poison => exact fun _ _ _ _ _ => ⟨_, rfl, trivial⟩
    | value q =>
      cases p' with
      | poison => exact (hp : False).elim
      | value q' =>
        cases (hp : q = q')
        exact StateRefinedBy.map (loadPtrResult lay ρ mp n)
          (fun h => ⟨decodePtr_isRefinedBy mp _ _ h, trivial⟩)
          (Fir.load_refines (unit := unitsOf lay) _ q _ _)

/-- `loadPtr` propagates poison with memory: a poison pointer gives no
result, and its UB is the UB of a pointer with no provenance, from the same
memories. -/
theorem loadPtr_memPropagates : MemPropagatesPoison (d := CoreDialect) (.loadPtr o mp a n) where
  poisonOut _ _ args hany _ _ _ h := by
    match args, hany with
    | .cons p .nil, hany =>
      have hp : p = .poison := hany.elim id False.elim
      subst hp
      exact nomatch h
  ubByOwnRules lay ρ args S _ hany _ := by
    match args, hany with
    | .cons p .nil, hany =>
      refine ⟨HVector.cons (f := toType) (a := Ty.ptr n) (.value ⟨none, 0⟩ : PoisonOr Pointer) .nil,
        ⟨?_, .inl ?_, trivial⟩, Fault.noProvenance.reason, ?_⟩
      · rintro (h | h) <;> cases h
      · exact hany.elim id False.elim
      · show (loadPtrResult lay ρ mp n <$> loadPtrAccess mp a n lay ρ ⟨none, 0⟩) S _
        exact (SetM.stateMap_apply _ _ S _).2 (.inr ⟨_, (Fir.load_apply _ _ _ _ S _).2
          (.inr ⟨.noProvenance, rfl, rfl⟩), rfl⟩)

/-- `loadPtr` gives a result from memories inside a call that hold a fresh
allocation of its units at its alignment, through the pointer to it: the
value its poison units decode to. -/
theorem loadPtr_memReturnsOnDefined : MemReturnsOnDefined (d := CoreDialect) (.loadPtr o mp a n) :=
  fun lay ρ => by
  let sh := ptrShape lay ρ mp a n
  let q := (Memories.empty : Memories _ (unitsOf lay)).enter.alloc (ρ n) .heap sh.1 sh.2
  have hl : q.2.load (ρ n) q.1 sh.1 sh.2 = .ok (List.replicate sh.1 .poison) := by
    show (q.2.mem (ρ n)).loadAligned q.1 sh.1 sh.2 = _
    rw [Memories.alloc_mem_self, Memories.alloc_fst]
    rw [Memory.loadAligned_of_aligned (by rw [← Memory.alloc_fst, Memory.aligned_alloc]; simp)]
    exact Memory.load_alloc _ _ (Int.le_refl 0) (by simp)
  refine ⟨HVector.cons (f := toType) (a := Ty.ptr n) (.value q.1 : PoisonOr Pointer) .nil, ?_, q.2,
    loadPtrResult lay ρ mp n (List.replicate sh.1 .poison), q.2, ?_, ?_⟩
  · rintro (h | h) <;> cases h
  · rw [Memories.alloc_frames (by decide)]
    exact List.cons_ne_nil _ _
  · show (loadPtrResult lay ρ mp n <$> loadPtrAccess mp a n lay ρ q.1) q.2 _
    exact (SetM.stateMap_apply _ _ q.2 _).2
      (.inl ⟨_, q.2, (Fir.load_apply _ _ _ _ q.2 _).2 (.inl ⟨_, hl, rfl⟩), rfl⟩)

end Fir.Core
