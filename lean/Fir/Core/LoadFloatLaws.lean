import Fir.Core.LoadLaws

/-!
# Float load obligations

`loadFloat` touches memory, so it meets each obligation with memory by its
own rule, as `load` does (the section on load obligations), wherever a run
names the core's memories and whatever their layout entries. Its rule is
`load`'s at the width of the float, `1 + e + m` bits, with the bits it
decodes given as the float with those bits, so each proof is `load`'s at
that width:

* _Effects._ It may be UB and may give poison, as it declares. It writes no
  unit of any memory, and allocates and frees in none. It reads no memory
  but the memory of its pointer.
* _Totality._ It has an outcome from any memories: UB, or a value.
* _Monotonicity._ A poison pointer is UB, which every outcome refines. On
  the same pointer, from memories that refine others, it faults for the
  same reason or loads units that refine the others', and their decoding
  refines the others' value (`decodeInt_isRefinedBy`).
* _Poison with memory._ A poison pointer gives no result, and its UB is the
  UB of a pointer with no provenance in its place, from the same memories.
  It gives a result from memories inside a call that hold an allocation of
  its units at its alignment.
* _Finitely many outcomes._ It has at most one that ends, from any
  memories.
-/

namespace Fir.Core

open Memory

variable (o : Memory.Ordering) (fe fm : Nat) (a : Option Nat) (n : Nat)

section

variable {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : Mem → N) (L : RunItems)

local notation "SM" => StateT (Memories N (unitsOf lay)) SetM

/-- `loadFloat` runs with memory by its rule. -/
theorem loadFloat_denote (p : PoisonOr Pointer) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L
    @Eq (SM (HVector toType [Ty.float fe fm]))
      (DialectDenote.denote (d := CoreDialect) (m := SM) (Op.loadFloat o fe fm a n) (.cons p .nil))
      (loadFloatRule lay ρ fe fm a n p) :=
  rfl

/-- On a poison pointer, `loadFloat`'s rule ends in UB, from any memories. -/
theorem loadFloatRule_poison (S : Memories N (unitsOf lay)) (e : Ev (HVector toType [Ty.float fe fm] ×
    Memories N (unitsOf lay))) : (loadFloatRule lay ρ fe fm a n .poison : SM _) S e ↔ e = .ub poisonPointer :=
  Iff.rfl

/-- On a pointer, `loadFloat`'s rule is its load, with the units decoded. -/
theorem loadFloatRule_value (p : Pointer) :
    (loadFloatRule lay ρ fe fm a n (.value p) : SM _) = loadFloatResult (lay (ρ n)) fe fm <$> loadAccess (floatWidth fe fm) a n lay ρ p :=
  rfl

/-- What `loadFloat` runs by its own rule has a property when its rule has it on
every pointer. -/
theorem loadFloat_ownRuleHas {P : {α : Type} → SM α → Prop}
    (h : ∀ p, P (loadFloatRule lay ρ fe fm a n p : SM (HVector toType [Ty.float fe fm]))) :
    OwnRuleHas lay ρ L P (d := CoreDialect) (.loadFloat o fe fm a n) := fun
  | .cons p .nil => ⟨fun _ => h p, fun h => nomatch h⟩

/-- `loadFloat` writes no unit of any memory. -/
theorem loadFloat_writesNot (x : N) :
    OwnRuleHas lay ρ L (WritesNot x) (d := CoreDialect) (.loadFloat o fe fm a n) :=
  loadFloat_ownRuleHas o fe fm a n lay ρ L fun
    | .poison => fun _ _ _ h => nomatch h
    | .value p => (Fir.load_writesNot (unit := unitsOf lay) _ p _ _ x).map _

/-- `loadFloat` neither allocates nor frees in any memory. -/
theorem loadFloat_allocatesNot (x : N) :
    OwnRuleHas lay ρ L (AllocatesNot x) (d := CoreDialect) (.loadFloat o fe fm a n) :=
  loadFloat_ownRuleHas o fe fm a n lay ρ L fun
    | .poison => fun _ _ _ h => nomatch h
    | .value p => (Fir.load_allocatesNot (unit := unitsOf lay) _ p _ _ x).map _

/-- `loadFloat` reads no memory but the memory of its pointer. -/
theorem loadFloat_readsNot (x : N)
    (hx : ¬ ((Fir.effects (d := CoreDialect) (.loadFloat o fe fm a n)).reads.map ρ).Has x) :
    OwnRuleHas lay ρ L (ReadsNot x) (d := CoreDialect) (.loadFloat o fe fm a n) :=
  loadFloat_ownRuleHas o fe fm a n lay ρ L fun
    | .poison => fun _ _ _ e he => by
      subst he
      exact ⟨_, rfl, rfl⟩
    | .value p => (Fir.load_readsNot (unit := unitsOf lay) _ p _ _
        fun h => hx (List.mem_singleton.2 h.symm)).map _

/-- `loadFloat` has an outcome from any memories. -/
theorem loadFloat_memTotal : MemTotal (d := CoreDialect) (.loadFloat o fe fm a n) := fun lay ρ L =>
  loadFloat_ownRuleHas o fe fm a n lay ρ L fun
    | .poison => fun _ => ⟨_, rfl⟩
    | .value p => (Fir.load_hasOutcome (unit := unitsOf lay) _ p _ _).map _

/-- `loadFloat` has at most one outcome that ends, from any memories. -/
theorem loadFloat_finitelyMany
    (args : HVector toType (Fir.sig (d := CoreDialect) (Op.loadFloat o fe fm a n))) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L
    FinitelyMany (DialectDenote.denote (d := CoreDialect)
      (m := SM) (Op.loadFloat o fe fm a n) args) := by
  match args with
  | .cons p .nil =>
    show FinitelyMany (loadFloatRule lay ρ fe fm a n p : SM _)
    cases (p : PoisonOr Pointer) with
    | poison => exact fun _ => ⟨[], fun _ h => nomatch h⟩
    | value q =>
      intro S
      obtain ⟨L, hL⟩ := Fir.load_finitelyMany (unit := unitsOf lay) (ρ n) q
        (loadShape (lay (ρ n)) (floatWidth fe fm) a).1 (loadShape (lay (ρ n)) (floatWidth fe fm) a).2 S
      refine ⟨L.map fun r => (loadFloatResult (lay (ρ n)) fe fm r.1, r.2), fun x hx => ?_⟩
      rcases (SetM.stateMap_apply _ _ S _).1 hx with ⟨us, S', hp, he⟩ | ⟨_, _, he⟩ <;> cases he
      exact List.mem_map.2 ⟨(us, S'), hL _ hp, rfl⟩

end

/-- From memories that refine others, `loadFloat` on a pointer that refines
another faults for the same reason or gives a value that refines the
other's; on a poison pointer it is UB, which every outcome refines. -/
theorem loadFloat_memMonotone : MemMonotone (d := CoreDialect) (.loadFloat o fe fm a n) := by
  intro N _ lay ρ L args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons p .nil, .cons p' .nil, ⟨hp, _⟩ =>
    show StateRefinedBy _ (loadFloatRule lay ρ fe fm a n p) (loadFloatRule lay ρ fe fm a n p')
    cases p with
    | poison => exact fun _ _ _ _ _ => ⟨_, rfl, trivial⟩
    | value q =>
      cases p' with
      | poison => exact (hp : False).elim
      | value q' =>
        cases (hp : q = q')
        exact StateRefinedBy.map (loadFloatResult (lay (ρ n)) fe fm)
          (fun h => ⟨decodeInt_isRefinedBy (floatWidth fe fm) _ h, trivial⟩)
          (Fir.load_refines (unit := unitsOf lay) _ q _ _)

/-- `loadFloat` propagates poison with memory: a poison pointer gives no result,
and its UB is the UB of a pointer with no provenance, from the same
memories. -/
theorem loadFloat_memPropagates : MemPropagatesPoison (d := CoreDialect) (.loadFloat o fe fm a n) where
  poisonOut _ _ _ args hany _ _ _ h := by
    match args, hany with
    | .cons p .nil, hany =>
      have hp : p = .poison := hany.elim id False.elim
      subst hp
      exact nomatch h
  ubByOwnRules lay ρ L args S _ hany _ := by
    match args, hany with
    | .cons p .nil, hany =>
      refine ⟨HVector.cons (f := toType) (a := Ty.ptr n) (.value ⟨none, 0⟩ : PoisonOr Pointer) .nil,
        ⟨?_, .inl ?_, trivial⟩, Fault.noProvenance.reason, ?_⟩
      · rintro (h | h) <;> cases h
      · exact hany.elim id False.elim
      · show (loadFloatResult (lay (ρ n)) fe fm <$> loadAccess (floatWidth fe fm) a n lay ρ ⟨none, 0⟩) S _
        exact (SetM.stateMap_apply _ _ S _).2 (.inr ⟨_, (Fir.load_apply _ _ _ _ S _).2
          (.inr ⟨.noProvenance, rfl, rfl⟩), rfl⟩)

/-- `loadFloat` gives a result from memories inside a call that hold a fresh
allocation of its units at its alignment, through the pointer to it: the
value its poison units decode to. -/
theorem loadFloat_memReturnsOnDefined : MemReturnsOnDefined (d := CoreDialect) (.loadFloat o fe fm a n) :=
  fun lay ρ L => by
  let sh := loadShape (lay (ρ n)) (floatWidth fe fm) a
  let q := (Memories.empty : Memories _ (unitsOf lay)).enter.alloc (ρ n) .heap sh.1 sh.2
  have hl : q.2.load (ρ n) q.1 sh.1 sh.2 = .ok (List.replicate sh.1 .poison) := by
    show (q.2.mem (ρ n)).loadAligned q.1 sh.1 sh.2 = _
    rw [Memories.alloc_mem_self, Memories.alloc_fst]
    rw [Memory.loadAligned_of_aligned (by rw [← Memory.alloc_fst, Memory.aligned_alloc]; simp)]
    exact Memory.load_alloc _ _ (Int.le_refl 0) (by simp)
  refine ⟨HVector.cons (f := toType) (a := Ty.ptr n) (.value q.1 : PoisonOr Pointer) .nil, ?_, q.2,
    loadFloatResult (lay (ρ n)) fe fm (List.replicate sh.1 .poison), q.2, ?_, ?_⟩
  · rintro (h | h) <;> cases h
  · rw [Memories.alloc_frames (by decide)]
    exact List.cons_ne_nil _ _
  · show (loadFloatResult (lay (ρ n)) fe fm <$> loadAccess (floatWidth fe fm) a n lay ρ q.1) q.2 _
    exact (SetM.stateMap_apply _ _ q.2 _).2
      (.inl ⟨_, q.2, (Fir.load_apply _ _ _ _ q.2 _).2 (.inl ⟨_, hl, rfl⟩), rfl⟩)

end Fir.Core
