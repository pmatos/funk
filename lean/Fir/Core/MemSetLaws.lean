import Fir.Core.MemRules
import Fir.Execution.MemoryChoiceLaws
import Fir.Execution.MemoryStoreLaws
import Fir.Execution.MemoryPoison

/-!
# Fill obligations

`memSet` touches memory, so it has no rule in the set monad and no tie to
it: it meets each obligation with memory by its own rule, wherever a run
names the core's memories and whatever their layout entries. For a defined
length its rule ends in one of three ways: at once with no result, for a
length of 0; in UB, on a poison pointer; or as a store in the state layer
of copies of the value's unit in the memory of its pointer, whose laws the
section on stores in the state layer proves. For a poison length it
chooses bits and runs the rule of their value, and the section on choices
in the state layer carries each law through that choice. So:

* _Effects._ It may be UB, as it declares, so that obligation asks nothing
  of it. It gives no result, so it makes no poison. It writes no memory
  but the memory of its pointer, the one it declares. It reads no memory,
  its own included, and allocates and frees in none.
* _Totality._ It has an outcome from any memories.
* _Monotonicity._ A poison pointer, with a length other than 0, is UB,
  which every outcome refines. On the same pointer and length, a value
  that refines another has a unit that refines the other's, so its copies
  do too, and the store refines from refining memories. A poison length
  may choose the value that refines it.
* _Finitely many outcomes._ It has at most one that ends for each length,
  and a poison length chooses one of finitely many.

The section on fill poison obligations gives the rest.
-/

namespace Fir.Core

open Memory

/-- The unit of a value that refines another refines the other's. -/
theorem setUnit_isRefinedBy (u : Nat) {v : Nat} {x x' : PoisonOr (BitVec v)} (h : x ⊑ x') :
    setUnit u x ⊑ setUnit u x' := by
  cases x with
  | poison => trivial
  | value b =>
    cases x' with
    | poison => exact (h : False).elim
    | value b' =>
      cases (h : b = b')
      exact MemUnit.isRefinedBy_refl _

/-- Copies of a unit that refines another refine as many copies of the
other. -/
theorem replicate_isRefinedBy {u : Nat} {a b : MemUnit u} (h : a ⊑ b) :
    ∀ len, List.replicate len a ⊑ List.replicate len b
  | 0 => trivial
  | len + 1 => ⟨h, replicate_isRefinedBy h len⟩

variable (o : Memory.Ordering) (v w n : Nat)

section

variable {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : Mem → N) (L : RunItems)

local notation "SM" => StateT (Memories N (unitsOf lay)) SetM

/-- `memSet` runs with memory by its rule. -/
theorem memSet_denote (p : PoisonOr Pointer) (x : PoisonOr (BitVec v)) (l : PoisonOr (BitVec w)) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L
    @Eq (SM (HVector toType ([] : List Ty)))
      (DialectDenote.denote (d := CoreDialect) (m := SM) (Op.memSet o v w n)
        (.cons p (.cons x (.cons l .nil))))
      (memSetRule lay ρ v w n p x l) :=
  rfl

/-- A property holds of the rule of a defined length when it holds of
giving no result, of UB, and of each store with no result. -/
theorem setLenRule_cases {P : SM (HVector toType ([] : List Ty)) → Prop}
    (hp : P (StateT.lift (pure .nil))) (hu : ∀ r, P (StateT.lift (MonadUB.ub r)))
    (hs : ∀ q us, P ((fun _ => .nil) <$> MonadMemory.store (m := SM) (ρ n) q us 1))
    (len : Nat) (p : PoisonOr Pointer) (x : PoisonOr (BitVec v)) :
    P (setLenRule lay ρ v n len p x) := by
  unfold setLenRule
  split
  · rw [SetM.statePure_lift]
    exact hp
  · cases p with
    | value q => exact hs _ _
    | poison =>
      show P (MonadUB.ub poisonSetPointer)
      rw [SetM.stateUB_lift]
      exact hu _

/-- A property holds of `memSet`'s rule when it holds of the rule of each
defined length, and is kept by a choice of bits. -/
theorem memSetRule_cases {P : SM (HVector toType ([] : List Ty)) → Prop}
    (hl : ∀ len p x, P (setLenRule lay ρ v n len p x))
    (hch : ∀ f : BitVec w → SM (HVector toType ([] : List Ty)), (∀ b, P (f b)) →
      P (MonadChoice.choose w >>= f))
    (p : PoisonOr Pointer) (x : PoisonOr (BitVec v)) :
    (l : PoisonOr (BitVec w)) → P (memSetRule lay ρ v w n p x l)
  | .value _ => hl _ _ _
  | .poison => hch _ fun _ => hl _ _ _

/-- What `memSet` runs by its own rule has a property when its rule has it
on every pointer, value and length. -/
theorem memSet_ownRuleHas {P : {α : Type} → SM α → Prop}
    (h : ∀ p x l, P (memSetRule lay ρ v w n p x l : SM (HVector toType ([] : List Ty)))) :
    OwnRuleHas lay ρ L P (d := CoreDialect) (.memSet o v w n) := fun
  | .cons p (.cons x (.cons l .nil)) => ⟨fun _ => h p x l, fun h => nomatch h⟩

/-- `memSet` writes no memory but the memory of its pointer. -/
theorem memSet_writesNot (y : N)
    (hy : ¬ ((Fir.effects (d := CoreDialect) (.memSet o v w n)).writes.map ρ).Has y) :
    OwnRuleHas lay ρ L (WritesNot y) (d := CoreDialect) (.memSet o v w n) :=
  memSet_ownRuleHas o v w n lay ρ L fun p x l =>
    memSetRule_cases v w n lay ρ
      (setLenRule_cases v n lay ρ (writesNot_lift y _) (fun _ => writesNot_lift y _)
        fun q us => (Fir.store_writesNot (unit := unitsOf lay) _ q us 1
          fun h => hy (List.mem_singleton.2 h.symm)).map _)
      (fun _ hf => WritesNot.chooseBind hf) p x l

/-- `memSet` reads no memory, its own included. -/
theorem memSet_readsNot (y : N) :
    OwnRuleHas lay ρ L (ReadsNot y) (d := CoreDialect) (.memSet o v w n) :=
  memSet_ownRuleHas o v w n lay ρ L fun p x l =>
    memSetRule_cases v w n lay ρ
      (setLenRule_cases v n lay ρ (readsNot_lift y _) (fun _ => readsNot_lift y _)
        fun q us => (Fir.store_readsNot (unit := unitsOf lay) _ q us 1 y).map _)
      (fun _ hf => ReadsNot.chooseBind hf) p x l

/-- `memSet` neither allocates nor frees in any memory. -/
theorem memSet_allocatesNot (y : N) :
    OwnRuleHas lay ρ L (AllocatesNot y) (d := CoreDialect) (.memSet o v w n) :=
  memSet_ownRuleHas o v w n lay ρ L fun p x l =>
    memSetRule_cases v w n lay ρ
      (setLenRule_cases v n lay ρ (allocatesNot_lift y _) (fun _ => allocatesNot_lift y _)
        fun q us => (Fir.store_allocatesNot (unit := unitsOf lay) _ q us 1 y).map _)
      (fun _ hf => AllocatesNot.chooseBind hf) p x l

/-- `memSet` has an outcome from any memories. -/
theorem memSet_memTotal : MemTotal (d := CoreDialect) (.memSet o v w n) := fun lay ρ L =>
  memSet_ownRuleHas o v w n lay ρ L fun p x l =>
    memSetRule_cases v w n lay ρ
      (setLenRule_cases v n lay ρ (hasOutcome_lift ⟨_, rfl⟩) (fun _ => hasOutcome_lift ⟨_, rfl⟩)
        fun q us => (Fir.store_hasOutcome (unit := unitsOf lay) _ q us 1).map _)
      (fun _ hf => HasOutcome.chooseBind hf) p x l

/-- `memSet` has finitely many outcomes that end, from any memories. -/
theorem memSet_finitelyMany
    (args : HVector toType (Fir.sig (d := CoreDialect) (Op.memSet o v w n))) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L
    FinitelyMany (DialectDenote.denote (d := CoreDialect)
      (m := SM) (Op.memSet o v w n) args) := by
  match args with
  | .cons p (.cons x (.cons l .nil)) =>
    refine memSetRule_cases v w n lay ρ (P := FinitelyMany)
      (setLenRule_cases v n lay ρ
        (FinitelyMany.lift ⟨[HVector.nil], fun _ h => by cases h; exact List.mem_singleton_self _⟩)
        (fun _ => FinitelyMany.lift ⟨[], fun _ h => nomatch h⟩) fun q us => ?_)
      (fun _ hf => FinitelyMany.chooseBind hf) p x l
    intro S
    obtain ⟨C, hC⟩ := Fir.store_finitelyMany (unit := unitsOf lay) (ρ n) q us 1 S
    refine ⟨C.map fun r => (HVector.nil, r.2), fun z hz => ?_⟩
    rcases (SetM.stateMap_apply _ _ S _).1 hz with ⟨u, S', hp, he⟩ | ⟨_, _, he⟩ <;> cases he
    exact List.mem_map.2 ⟨(u, S'), hC _ hp, rfl⟩

/-- On the same length, a pointer and a value that refine others give a
rule that refines the others'. -/
theorem setLenRule_refines (len : Nat) {p p' : PoisonOr Pointer} {x x' : PoisonOr (BitVec v)}
    (hp : PoisonOr.IsRefinedBy p p') (hx : x ⊑ x') :
    StateRefinedBy (HVector.Forall₂ TyRefinement.IsRefinedBy)
      (setLenRule (m := SM) lay ρ v n len p x) (setLenRule lay ρ v n len p' x') := by
  unfold setLenRule
  split
  · exact fun S S' hS e he => by cases he; exact ⟨_, rfl, trivial, hS⟩
  · cases p with
    | poison => exact fun _ _ _ _ _ => ⟨_, rfl, trivial⟩
    | value q =>
      cases p' with
      | poison => exact (hp : False).elim
      | value q' =>
        cases (hp : q = q')
        exact StateRefinedBy.map (fun _ => HVector.nil) (fun _ => trivial)
          (Fir.store_refines (unit := unitsOf lay) _ q _
            (replicate_isRefinedBy (setUnit_isRefinedBy _ hx) len))

end

/-- To memories that refine others, `memSet` on operands that refine
others faults for the same reason or gives memories that refine the
others'; a poison pointer with a length other than 0 is UB, which every
outcome refines, and a poison length may choose the value that refines
it. -/
theorem memSet_memMonotone : MemMonotone (d := CoreDialect) (.memSet o v w n) := by
  intro N _ lay ρ L args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons p (.cons x (.cons l .nil)), .cons p' (.cons x' (.cons l' .nil)), ⟨hp, hx, hl, _⟩ =>
    show StateRefinedBy _ (memSetRule lay ρ v w n p x l) (memSetRule lay ρ v w n p' x' l')
    cases l with
    | poison =>
      cases l' with
      | poison => exact StateRefinedBy.chooseBind fun _ => setLenRule_refines v n lay ρ _ hp hx
      | value b => exact StateRefinedBy.chooseBind_left b (setLenRule_refines v n lay ρ _ hp hx)
    | value b =>
      cases l' with
      | poison => exact (hl : False).elim
      | value b' =>
        cases (hl : b = b')
        exact setLenRule_refines v n lay ρ _ hp hx

end Fir.Core
