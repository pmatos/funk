import Fir.Core.MemRules
import Fir.Execution.MemoryChoiceLaws
import Fir.Execution.MemoryPoison

/-!
# Copy and move obligations

`memCopy` touches memory, so it has no rule in the set monad and no tie to
it: it meets each obligation with memory by its own rule, wherever a run
names the core's memories and whatever their layout entries. For a defined
length its rule ends in one of three ways: at once with no result, for a
length of 0; in UB, on a poison pointer or a copy whose ranges partly
overlap; or as the copy of units in the memory of its pointers, whose laws
the section on copies of units in the state layer proves. For a poison
length it chooses bits and runs the rule of their value, and the section on
choices in the state layer carries each law through that choice. So:

* _Effects._ It may be UB, as it declares, so that obligation asks nothing
  of it. It gives no result, so it makes no poison. It writes and reads no
  memory but the memory of its pointers, the one it declares, and
  allocates and frees in none.
* _Totality._ It has an outcome from any memories.
* _Monotonicity._ A poison pointer, with a length other than 0, is UB,
  which every outcome refines. On the same pointers and length the rule is
  the same, and the copy of units refines from refining memories. A poison
  length may choose the value that refines it.
* _Finitely many outcomes._ It has at most one that ends for each length,
  and a poison length chooses one of finitely many.

The section on copy and move poison obligations gives the rest.
-/

namespace Fir.Core

open Memory

variable (k : CopyKind) (o : Memory.Ordering) (w n : Nat)

section

variable {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : Mem → N) (L : RunItems)

local notation "SM" => StateT (Memories N (unitsOf lay)) SetM

/-- `memCopy` runs with memory by its rule. -/
theorem memCopy_denote (d s : PoisonOr Pointer) (l : PoisonOr (BitVec w)) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L
    @Eq (SM (HVector toType ([] : List Ty)))
      (DialectDenote.denote (d := CoreDialect) (m := SM) (Op.memCopy k o w n)
        (.cons d (.cons s (.cons l .nil))))
      (memCopyRule lay ρ k w n d s l) :=
  rfl

omit [DecidableEq N] in
/-- `pure` in the state layer is the lift of `pure`. -/
theorem stateM_pure_lift {α : Type} (a : α) : (pure a : SM α) = StateT.lift (pure a) :=
  funext fun S => (SetM.pure_bind a fun b => (pure (b, S) : SetM _)).symm

omit [DecidableEq N] in
/-- UB in the state layer is the lift of UB. -/
theorem stateM_ub_lift {α : Type} (r : String) : (MonadUB.ub r : SM α) = StateT.lift (MonadUB.ub r) :=
  funext fun _ => (SetM.ub_bind r _).symm

/-- A property holds of the rule of a defined length when it holds of
giving no result, of UB, and of the copy of units with no result. -/
theorem copyLenRule_cases {P : SM (HVector toType ([] : List Ty)) → Prop}
    (hp : P (StateT.lift (pure .nil))) (hu : ∀ r, P (StateT.lift (MonadUB.ub r)))
    (hc : ∀ d s len, P ((fun _ => .nil) <$> copyUnits (m := SM) (ρ n) d s len 1 1))
    (len : Nat) (d s : PoisonOr Pointer) : P (copyLenRule lay ρ k n len d s) := by
  unfold copyLenRule
  split
  · rw [stateM_pure_lift]
    exact hp
  · match d, s with
    | .value d, .value s =>
      dsimp only
      split
      · rw [stateM_ub_lift]
        exact hu _
      · exact hc _ _ _
    | .poison, _ | .value _, .poison =>
      show P (MonadUB.ub poisonCopyPointer)
      rw [stateM_ub_lift]
      exact hu _

/-- A property holds of `memCopy`'s rule when it holds of the rule of each
defined length, and is kept by a choice of bits. -/
theorem memCopyRule_cases {P : SM (HVector toType ([] : List Ty)) → Prop}
    (hl : ∀ len d s, P (copyLenRule lay ρ k n len d s))
    (hch : ∀ f : BitVec w → SM (HVector toType ([] : List Ty)), (∀ b, P (f b)) →
      P (MonadChoice.choose w >>= f))
    (d s : PoisonOr Pointer) : (l : PoisonOr (BitVec w)) → P (memCopyRule lay ρ k w n d s l)
  | .value _ => hl _ _ _
  | .poison => hch _ fun _ => hl _ _ _

/-- What `memCopy` runs by its own rule has a property when its rule has
it on every pointer and length. -/
theorem memCopy_ownRuleHas {P : {α : Type} → SM α → Prop}
    (h : ∀ d s l, P (memCopyRule lay ρ k w n d s l : SM (HVector toType ([] : List Ty)))) :
    OwnRuleHas lay ρ L P (d := CoreDialect) (.memCopy k o w n) := fun
  | .cons d (.cons s (.cons l .nil)) => ⟨fun _ => h d s l, fun h => nomatch h⟩

/-- `memCopy` writes no memory but the memory of its pointers. -/
theorem memCopy_writesNot (x : N)
    (hx : ¬ ((Fir.effects (d := CoreDialect) (.memCopy k o w n)).writes.map ρ).Has x) :
    OwnRuleHas lay ρ L (WritesNot x) (d := CoreDialect) (.memCopy k o w n) :=
  memCopy_ownRuleHas k o w n lay ρ L fun d s l =>
    memCopyRule_cases k w n lay ρ
      (copyLenRule_cases k n lay ρ (writesNot_lift x _) (fun _ => writesNot_lift x _)
        fun d s len => (copyUnits_writesNot (unit := unitsOf lay) _ d s len 1 1
          fun h => hx (List.mem_singleton.2 h.symm)).map _)
      (fun _ hf => WritesNot.chooseBind hf) d s l

/-- `memCopy` reads no memory but the memory of its pointers. -/
theorem memCopy_readsNot (x : N)
    (hx : ¬ ((Fir.effects (d := CoreDialect) (.memCopy k o w n)).reads.map ρ).Has x) :
    OwnRuleHas lay ρ L (ReadsNot x) (d := CoreDialect) (.memCopy k o w n) :=
  memCopy_ownRuleHas k o w n lay ρ L fun d s l =>
    memCopyRule_cases k w n lay ρ
      (copyLenRule_cases k n lay ρ (readsNot_lift x _) (fun _ => readsNot_lift x _)
        fun d s len => (copyUnits_readsNot (unit := unitsOf lay) _ d s len 1 1
          fun h => hx (List.mem_singleton.2 h.symm)).map _)
      (fun _ hf => ReadsNot.chooseBind hf) d s l

/-- `memCopy` neither allocates nor frees in any memory. -/
theorem memCopy_allocatesNot (x : N) :
    OwnRuleHas lay ρ L (AllocatesNot x) (d := CoreDialect) (.memCopy k o w n) :=
  memCopy_ownRuleHas k o w n lay ρ L fun d s l =>
    memCopyRule_cases k w n lay ρ
      (copyLenRule_cases k n lay ρ (allocatesNot_lift x _) (fun _ => allocatesNot_lift x _)
        fun d s len => (copyUnits_allocatesNot (unit := unitsOf lay) _ d s len 1 1 x).map _)
      (fun _ hf => AllocatesNot.chooseBind hf) d s l

/-- `memCopy` has an outcome from any memories. -/
theorem memCopy_memTotal : MemTotal (d := CoreDialect) (.memCopy k o w n) := fun lay ρ L =>
  memCopy_ownRuleHas k o w n lay ρ L fun d s l =>
    memCopyRule_cases k w n lay ρ
      (copyLenRule_cases k n lay ρ (hasOutcome_lift ⟨_, rfl⟩) (fun _ => hasOutcome_lift ⟨_, rfl⟩)
        fun d s len => (copyUnits_hasOutcome (unit := unitsOf lay) _ d s len 1 1).map _)
      (fun _ hf => HasOutcome.chooseBind hf) d s l

/-- `memCopy` has finitely many outcomes that end, from any memories. -/
theorem memCopy_finitelyMany
    (args : HVector toType (Fir.sig (d := CoreDialect) (Op.memCopy k o w n))) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L
    FinitelyMany (DialectDenote.denote (d := CoreDialect)
      (m := SM) (Op.memCopy k o w n) args) := by
  match args with
  | .cons d (.cons s (.cons l .nil)) =>
    refine memCopyRule_cases k w n lay ρ (P := FinitelyMany)
      (copyLenRule_cases k n lay ρ
        (FinitelyMany.lift ⟨[HVector.nil], fun _ h => by cases h; exact List.mem_singleton_self _⟩)
        (fun _ => FinitelyMany.lift ⟨[], fun _ h => nomatch h⟩) fun d s len => ?_)
      (fun _ hf => FinitelyMany.chooseBind hf) d s l
    intro S
    obtain ⟨C, hC⟩ := copyUnits_finitelyMany (unit := unitsOf lay) (ρ n) d s len 1 1 S
    refine ⟨C.map fun r => (HVector.nil, r.2), fun x hx => ?_⟩
    rcases (SetM.stateMap_apply _ _ S _).1 hx with ⟨u, S', hp, he⟩ | ⟨_, _, he⟩ <;> cases he
    exact List.mem_map.2 ⟨(u, S'), hC _ hp, rfl⟩

/-- On the same length, pointers that refine others give a rule that
refines the others'. -/
theorem copyLenRule_refines (len : Nat) {d s d' s' : PoisonOr Pointer}
    (hd : PoisonOr.IsRefinedBy d d') (hs : PoisonOr.IsRefinedBy s s') :
    StateRefinedBy (HVector.Forall₂ TyRefinement.IsRefinedBy)
      (copyLenRule (m := SM) lay ρ k n len d s) (copyLenRule lay ρ k n len d' s') := by
  unfold copyLenRule
  split
  · exact fun S S' hS e he => by cases he; exact ⟨_, rfl, trivial, hS⟩
  · match d, s, d', s', hd, hs with
    | .value d, .value s, .value d', .value s', hd, hs =>
      cases (hd : d = d')
      cases (hs : s = s')
      dsimp only
      split
      · exact fun _ _ _ _ _ => ⟨_, rfl, trivial⟩
      · exact StateRefinedBy.map (fun _ => HVector.nil) (fun _ => trivial)
          (copyUnits_refines (unit := unitsOf lay) _ d s len 1 1)
    | .poison, _, _, _, _, _ | .value _, .poison, _, _, _, _ =>
      exact fun _ _ _ _ _ => ⟨_, rfl, trivial⟩

end

/-- To memories that refine others, `memCopy` on operands that refine
others faults for the same reason or gives memories that refine the
others'; a poison pointer with a length other than 0 is UB, which every
outcome refines, and a poison length may choose the value that refines
it. -/
theorem memCopy_memMonotone : MemMonotone (d := CoreDialect) (.memCopy k o w n) := by
  intro N _ lay ρ L args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons d (.cons s (.cons l .nil)), .cons d' (.cons s' (.cons l' .nil)), ⟨hd, hs, hl, _⟩ =>
    show StateRefinedBy _ (memCopyRule lay ρ k w n d s l) (memCopyRule lay ρ k w n d' s' l')
    cases l with
    | poison =>
      cases l' with
      | poison => exact StateRefinedBy.chooseBind fun _ => copyLenRule_refines k n lay ρ _ hd hs
      | value v => exact StateRefinedBy.chooseBind_left v (copyLenRule_refines k n lay ρ _ hd hs)
    | value v =>
      cases l' with
      | poison => exact (hl : False).elim
      | value v' =>
        cases (hl : v = v')
        exact copyLenRule_refines k n lay ρ _ hd hs

end Fir.Core
