import Fir.Core.MemRules
import Fir.Execution.MemoryFromAddrLaws
import Fir.Execution.MemoryChoiceLaws
import Fir.Execution.MemoryPoison

/-!
# Pointers as integers: obligations

`ptrExpose` and `ptrFromInt` touch memory, so they have no rule in the set
monad and no tie to it: each meets each obligation with memory by its own
rule, wherever a run names the core's memories, whatever their layout
entries and whatever the items, the address policies and resolvers
included, that the run gives. `ptrExpose`'s rule is UB on a poison
pointer, and otherwise the exposure of the state layer, whose laws the
section on exposing in the state layer proves. `ptrFromInt`'s rule is the
turning of an integer back into a pointer in the state layer, whose laws
the section on turning integers into pointers in the state layer proves,
with its result mapped. So:

* _Effects._ `ptrExpose` may be UB, as it declares, and `ptrFromInt` is
  never UB. On a defined operand each gives a defined result, so neither
  makes poison. Neither writes a unit of any memory, nor allocates or
  frees in any memory. Each reads no memory but the memory of its
  pointer, the one it declares. `ptrExpose` gives no address in another
  memory, and counts no rebuild in any; `ptrFromInt` gives no address in
  any memory, and counts no rebuild in another memory.
* _Totality._ Each has an outcome from any memories.
* _Monotonicity._ A poison pointer of `ptrExpose` is UB, which every
  outcome refines; on the same pointer, exposures in memories that refine
  others give the same integer, or UB in both. `ptrFromInt` on the same
  integer gives the same pointer, and on a poison integer gives poison,
  which every pointer refines; either way it counts the call, so the
  memories after refine the others'.
* _Finitely many outcomes._ Each has at most one that ends.

`ptrFromInt` propagates poison: a poison integer gives a poison pointer,
and it is never UB. It returns a result on every integer, from any
memories. `ptrExpose` is an exception, so it has no poison obligation (the
section on the poison classes of the core ops).
-/

namespace Fir.Core

open Memory

/-- Mapping the results keeps finitely many outcomes. -/
theorem finitelyMany_map {σ α β : Type} (f : α → β) {c : StateT σ SetM α} (h : FinitelyMany c) :
    FinitelyMany (f <$> c) := fun S => by
  obtain ⟨C, hC⟩ := h S
  refine ⟨C.map fun r => (f r.1, r.2), fun z hz => ?_⟩
  rcases (SetM.stateMap_apply f c S _).1 hz with ⟨a, S', hp, he⟩ | ⟨_, _, he⟩ <;> cases he
  exact List.mem_map.2 ⟨(a, S'), hC _ hp, rfl⟩

variable (n w : Nat)

section

variable {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : Mem → N) (L : RunItems)

local notation "SM" => StateT (Memories N (unitsOf lay)) SetM

/-- The exposure that `ptrExpose`'s rule runs on the pointer `q`. -/
abbrev exposeAt (q : Pointer) : SM (BitVec (lay (ρ n)).pointer) :=
  MonadMemory.expose (ρ n) (L.addrs n) (lay (ρ n)).pointer q

/-- The turning back of an integer that `ptrFromInt`'s rule runs on the
address `a`. -/
abbrev fromAddrAt (a : BitVec (lay (ρ n)).pointer) : SM Pointer :=
  MonadMemory.fromAddr (ρ n) (L.resolvers n) (lay (ρ n)).pointer a

/-- A property holds of `ptrExpose`'s rule when it holds of UB and of each
exposure with its result mapped. -/
theorem ptrExposeRule_cases {P : SM (HVector toType [Ty.int w]) → Prop}
    (hu : ∀ r, P (StateT.lift (MonadUB.ub r)))
    (he : ∀ (f : BitVec (lay (ρ n)).pointer → HVector toType [Ty.int w]) q,
      P (f <$> exposeAt n lay ρ L q)) (p : PoisonOr Pointer) :
    P (ptrExposeRule lay ρ L n w p) := by
  cases p with
  | value q => exact he _ q
  | poison =>
    show P (MonadUB.ub poisonExposePointer)
    rw [SetM.stateUB_lift]
    exact hu _

/-- A property holds of `ptrFromInt`'s rule when it holds of each turning
back of an integer with its result mapped. -/
theorem ptrFromIntRule_cases {P : SM (HVector toType [Ty.ptr n]) → Prop}
    (hf : ∀ (f : Pointer → HVector toType [Ty.ptr n]) a, P (f <$> fromAddrAt n lay ρ L a))
    (i : PoisonOr (BitVec w)) : P (ptrFromIntRule lay ρ L n w i) := by
  cases i <;> exact hf _ _

/-- What `ptrExpose` runs by its own rule has a property when its rule has
it on every pointer. -/
theorem ptrExpose_ownRuleHas {P : {α : Type} → SM α → Prop}
    (h : ∀ p, P (ptrExposeRule lay ρ L n w p : SM (HVector toType [Ty.int w]))) :
    OwnRuleHas lay ρ L P (d := CoreDialect) (.ptrExpose n w) := fun
  | .cons p .nil => ⟨fun _ => h p, fun h => nomatch h⟩

/-- What `ptrFromInt` runs by its own rule has a property when its rule has
it on every integer. -/
theorem ptrFromInt_ownRuleHas {P : {α : Type} → SM α → Prop}
    (h : ∀ i, P (ptrFromIntRule lay ρ L n w i : SM (HVector toType [Ty.ptr n]))) :
    OwnRuleHas lay ρ L P (d := CoreDialect) (.ptrFromInt n w) := fun
  | .cons i .nil => ⟨fun _ => h i, fun h => nomatch h⟩

omit [DecidableEq N] in
/-- A memory that an op of the memory `n` does not declare is not `ρ n`. -/
theorem ne_of_not_has {s : MemSet Mem} (hs : s = .these [n]) {y : N}
    (hy : ¬ (s.map ρ).Has y) : ρ n ≠ y := fun h => hy (by subst hs h; exact List.mem_singleton_self _)

/-- `ptrExpose` writes no unit of any memory. -/
theorem ptrExpose_writesNot (y : N) :
    OwnRuleHas lay ρ L (WritesNot y) (d := CoreDialect) (.ptrExpose n w) :=
  ptrExpose_ownRuleHas n w lay ρ L fun p => ptrExposeRule_cases n w lay ρ L
    (fun _ => writesNot_lift y _) (fun f q => (Fir.expose_writesNot _ _ _ q y).map f) p

/-- `ptrExpose` reads no memory but the memory of its pointer. -/
theorem ptrExpose_readsNot (y : N)
    (hy : ¬ ((Fir.effects (d := CoreDialect) (.ptrExpose n w)).reads.map ρ).Has y) :
    OwnRuleHas lay ρ L (ReadsNot y) (d := CoreDialect) (.ptrExpose n w) :=
  ptrExpose_ownRuleHas n w lay ρ L fun p => ptrExposeRule_cases n w lay ρ L
    (fun _ => readsNot_lift y _)
    (fun f q => (Fir.expose_readsNot_ne _ _ _ q (ne_of_not_has n ρ rfl hy)).map f) p

/-- `ptrExpose` neither allocates nor frees in any memory. -/
theorem ptrExpose_allocatesNot (y : N) :
    OwnRuleHas lay ρ L (AllocatesNot y) (d := CoreDialect) (.ptrExpose n w) :=
  ptrExpose_ownRuleHas n w lay ρ L fun p => ptrExposeRule_cases n w lay ρ L
    (fun _ => allocatesNot_lift y _) (fun f q => (Fir.expose_allocatesNot _ _ _ q y).map f) p

/-- `ptrExpose` gives no address in any memory but the memory of its
pointer. -/
theorem ptrExpose_exposesNot (y : N)
    (hy : ¬ ((Fir.effects (d := CoreDialect) (.ptrExpose n w)).allocates.map ρ).Has y) :
    OwnRuleHas lay ρ L (ExposesNot y) (d := CoreDialect) (.ptrExpose n w) :=
  ptrExpose_ownRuleHas n w lay ρ L fun p => ptrExposeRule_cases n w lay ρ L
    (fun _ => exposesNot_lift _)
    (fun f q => (Fir.expose_exposesNot _ _ _ q (ne_of_not_has n ρ rfl hy)).map f) p

/-- `ptrExpose` counts no rebuild in any memory. -/
theorem ptrExpose_rebuildsNot (y : N) :
    OwnRuleHas lay ρ L (RebuildsNot y) (d := CoreDialect) (.ptrExpose n w) :=
  ptrExpose_ownRuleHas n w lay ρ L fun p => ptrExposeRule_cases n w lay ρ L
    (fun _ => rebuildsNot_lift _) (fun f q => (Fir.expose_rebuildsNot _ _ _ q y).map f) p

/-- `ptrFromInt` writes no unit of any memory. -/
theorem ptrFromInt_writesNot (y : N) :
    OwnRuleHas lay ρ L (WritesNot y) (d := CoreDialect) (.ptrFromInt n w) :=
  ptrFromInt_ownRuleHas n w lay ρ L fun i => ptrFromIntRule_cases n w lay ρ L
    (fun f a => (Fir.fromAddr_writesNot _ _ _ a y).map f) i

/-- `ptrFromInt` reads no memory but the memory of its pointer. -/
theorem ptrFromInt_readsNot (y : N)
    (hy : ¬ ((Fir.effects (d := CoreDialect) (.ptrFromInt n w)).reads.map ρ).Has y) :
    OwnRuleHas lay ρ L (ReadsNot y) (d := CoreDialect) (.ptrFromInt n w) :=
  ptrFromInt_ownRuleHas n w lay ρ L fun i => ptrFromIntRule_cases n w lay ρ L
    (fun f a => (Fir.fromAddr_readsNot_ne _ _ _ a (ne_of_not_has n ρ rfl hy)).map f) i

/-- `ptrFromInt` neither allocates nor frees in any memory. -/
theorem ptrFromInt_allocatesNot (y : N) :
    OwnRuleHas lay ρ L (AllocatesNot y) (d := CoreDialect) (.ptrFromInt n w) :=
  ptrFromInt_ownRuleHas n w lay ρ L fun i => ptrFromIntRule_cases n w lay ρ L
    (fun f a => (Fir.fromAddr_allocatesNot _ _ _ a y).map f) i

/-- `ptrFromInt` gives no address in any memory. -/
theorem ptrFromInt_exposesNot (y : N) :
    OwnRuleHas lay ρ L (ExposesNot y) (d := CoreDialect) (.ptrFromInt n w) :=
  ptrFromInt_ownRuleHas n w lay ρ L fun i => ptrFromIntRule_cases n w lay ρ L
    (fun f a => (Fir.fromAddr_exposesNot _ _ _ a y).map f) i

/-- `ptrFromInt` counts no rebuild in any memory but the memory of its
pointer. -/
theorem ptrFromInt_rebuildsNot (y : N)
    (hy : ¬ ((Fir.effects (d := CoreDialect) (.ptrFromInt n w)).allocates.map ρ).Has y) :
    OwnRuleHas lay ρ L (RebuildsNot y) (d := CoreDialect) (.ptrFromInt n w) :=
  ptrFromInt_ownRuleHas n w lay ρ L fun i => ptrFromIntRule_cases n w lay ρ L
    (fun f a => (Fir.fromAddr_rebuildsNot _ _ _ a (ne_of_not_has n ρ rfl hy)).map f) i

/-- `ptrExpose` has finitely many outcomes that end, from any memories. -/
theorem ptrExpose_finitelyMany
    (args : HVector toType (Fir.sig (d := CoreDialect) (Op.ptrExpose n w))) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L
    FinitelyMany (DialectDenote.denote (d := CoreDialect) (m := SM) (Op.ptrExpose n w) args) := by
  match args with
  | .cons p .nil =>
    exact ptrExposeRule_cases n w lay ρ L (P := FinitelyMany)
      (fun _ => FinitelyMany.lift ⟨[], fun _ h => nomatch h⟩)
      (fun f q => finitelyMany_map f (Fir.expose_finitelyMany _ _ _ q)) p

/-- `ptrFromInt` has one outcome, from any memories. -/
theorem ptrFromInt_finitelyMany
    (args : HVector toType (Fir.sig (d := CoreDialect) (Op.ptrFromInt n w))) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L
    FinitelyMany (DialectDenote.denote (d := CoreDialect) (m := SM) (Op.ptrFromInt n w) args) := by
  match args with
  | .cons i .nil =>
    exact ptrFromIntRule_cases n w lay ρ L (P := FinitelyMany)
      (fun f a => finitelyMany_map f (Fir.fromAddr_finitelyMany _ _ _ a)) i

/-- Two turnings back of integers, each with its result mapped, refine each
other whenever every result of the one is related to every result of the
other: each counts the call, so the memories after refine. -/
theorem fromAddrAt_refines {β : Type} {r : β → β → Prop}
    (f g : Pointer → β) (hfg : ∀ p q, r (f p) (g q)) (a b : BitVec (lay (ρ n)).pointer) :
    StateRefinedBy r (f <$> fromAddrAt n lay ρ L a) (g <$> fromAddrAt n lay ρ L b) := by
  intro S S' hS e he
  rcases (SetM.stateMap_apply _ _ S' e).1 he with ⟨q, T', hq, rfl⟩ | ⟨_, hu, -⟩
  · cases (Fir.fromAddr_apply _ _ _ _ S' _).1 hq
    refine ⟨.ok (f (S.fromAddr (ρ n) (L.resolvers n) _ a).1,
      (S.fromAddr (ρ n) (L.resolvers n) _ a).2),
      (SetM.stateMap_apply _ _ S _).2 (.inl ⟨_, _, (Fir.fromAddr_apply _ _ _ _ S _).2 rfl, rfl⟩),
      hfg _ _, ?_⟩
    exact (Memories.IsRefinedBy.fromAddr hS (ρ n) (L.resolvers n) _ b).2
  · exact absurd hu (Fir.fromAddr_noUB _ _ _ _ S' _)

end

/-- `ptrFromInt` never ends in UB. -/
theorem ptrFromInt_neverUB : NeverUB (d := CoreDialect) (.ptrFromInt n w) := fun lay ρ L =>
  ptrFromInt_ownRuleHas n w lay ρ L fun i => ptrFromIntRule_cases n w lay ρ L
    (fun f a => (Fir.fromAddr_noUB (unit := unitsOf lay) _ _ _ a).map f) i

/-- `ptrExpose` gives a defined integer on a defined pointer. -/
theorem ptrExpose_makesNoPoison : MakesNoPoison (d := CoreDialect) (.ptrExpose n w) := by
  intro _ N _ lay ρ L args hp S rs S' h
  match args, hp, h with
  | .cons (.value q) .nil, _, h =>
    have h : ptrExposeRule (m := StateT (Memories N (unitsOf lay)) SetM) lay ρ L n w (.value q) S
      (.ok (rs, S')) := h
    rcases (SetM.stateMap_apply _ _ S _).1 h with ⟨_, _, _, he⟩ | ⟨_, _, he⟩ <;> cases he
    exact fun h => by rcases h with h | h <;> cases h
  | .cons .poison .nil, hp, _ => exact absurd (.inl rfl) hp

/-- `ptrFromInt` gives a defined pointer on a defined integer. -/
theorem ptrFromInt_makesNoPoison : MakesNoPoison (d := CoreDialect) (.ptrFromInt n w) := by
  intro _ N _ lay ρ L args hp S rs S' h
  match args, hp, h with
  | .cons (.value b) .nil, _, h =>
    have h : ptrFromIntRule (m := StateT (Memories N (unitsOf lay)) SetM) lay ρ L n w (.value b) S
      (.ok (rs, S')) := h
    rcases (SetM.stateMap_apply _ _ S _).1 h with ⟨_, _, _, he⟩ | ⟨_, _, he⟩ <;> cases he
    exact fun h => by rcases h with h | h <;> cases h
  | .cons .poison .nil, hp, _ => exact absurd (.inl rfl) hp

/-- `ptrExpose` has an outcome from any memories. -/
theorem ptrExpose_memTotal : MemTotal (d := CoreDialect) (.ptrExpose n w) := fun lay ρ L =>
  ptrExpose_ownRuleHas n w lay ρ L fun p => ptrExposeRule_cases n w lay ρ L
    (fun _ => hasOutcome_lift ⟨_, rfl⟩)
    (fun f q => (Fir.expose_hasOutcome (unit := unitsOf lay) _ _ _ q).map f) p

/-- `ptrFromInt` has an outcome from any memories. -/
theorem ptrFromInt_memTotal : MemTotal (d := CoreDialect) (.ptrFromInt n w) := fun lay ρ L =>
  ptrFromInt_ownRuleHas n w lay ρ L fun i => ptrFromIntRule_cases n w lay ρ L
    (fun f a => (Fir.fromAddr_hasOutcome (unit := unitsOf lay) _ _ _ a).map f) i

/-- `ptrExpose` is monotone with memory: a poison pointer is UB, which every
outcome refines, and on the same pointer, exposures in memories that
refine others give the same integer, or UB in both, and memories that
refine the others'. -/
theorem ptrExpose_memMonotone : MemMonotone (d := CoreDialect) (.ptrExpose n w) := by
  intro N _ lay ρ L args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons p .nil, .cons p' .nil, ⟨hp, _⟩ =>
    show StateRefinedBy _ (ptrExposeRule lay ρ L n w p) (ptrExposeRule lay ρ L n w p')
    cases p with
    | poison => exact fun _ _ _ _ _ => ⟨_, rfl, trivial⟩
    | value q =>
      cases p' with
      | poison => exact (hp : False).elim
      | value q' =>
        cases (hp : q = q')
        exact StateRefinedBy.map _ (fun h => by cases h; exact ⟨rfl, trivial⟩)
          (Fir.expose_refines (unit := unitsOf lay) _ _ _ q)

/-- `ptrFromInt` is monotone with memory: on the same integer it gives the
same pointer, and on a poison integer poison, which every pointer refines;
either way it counts the call, so the memories after refine the others'. -/
theorem ptrFromInt_memMonotone : MemMonotone (d := CoreDialect) (.ptrFromInt n w) := by
  intro N _ lay ρ L args args' h
  refine ⟨fun _ => ?_, fun h => nomatch h⟩
  match args, args', h with
  | .cons i .nil, .cons i' .nil, ⟨hi, _⟩ =>
    show StateRefinedBy _ (ptrFromIntRule lay ρ L n w i) (ptrFromIntRule lay ρ L n w i')
    cases i with
    | poison =>
      cases i' <;> exact fromAddrAt_refines n lay ρ L _ _ (fun _ _ => ⟨trivial, trivial⟩) _ _
    | value b =>
      cases i' with
      | poison => exact (hi : False).elim
      | value b' =>
        cases (hi : b = b')
        exact StateRefinedBy.map _ (fun h => by cases h; exact ⟨rfl, trivial⟩)
          (Fir.fromAddr_refines (unit := unitsOf lay) _ _ _ _)

/-- `ptrFromInt` propagates poison with memory: a poison integer gives a
poison pointer, and it is never UB. -/
theorem ptrFromInt_memPropagates : MemPropagatesPoison (d := CoreDialect) (.ptrFromInt n w) where
  poisonOut lay ρ L args hany S rs S' h := by
    match args, hany, h with
    | .cons .poison .nil, _, h =>
      have h : ptrFromIntRule (m := StateT (Memories _ (unitsOf lay)) SetM) lay ρ L n w .poison S
        (.ok (rs, S')) := h
      rcases (SetM.stateMap_apply _ _ S _).1 h with ⟨_, _, _, he⟩ | ⟨_, _, he⟩ <;> cases he
      exact ⟨rfl, trivial⟩
    | .cons (.value _) .nil, hany, _ => rcases hany with h | h <;> cases h
  ubByOwnRules lay ρ L args S r _ hub :=
    absurd hub ((ptrFromInt_neverUB n w lay ρ L args).1 rfl S r)

/-- `ptrFromInt` returns a result on a defined integer, from any memories. -/
theorem ptrFromInt_memReturnsOnDefined :
    MemReturnsOnDefined (d := CoreDialect) (.ptrFromInt n w) := fun lay ρ L => by
  refine ⟨HVector.cons (f := toType) (a := Ty.int w) (.value 0#w : PoisonOr (BitVec w)) .nil,
    ?_, Memories.empty.enter, ?_⟩
  · rintro (h | h) <;> cases h
  · let S := (Memories.empty.enter : Memories _ (unitsOf lay)).fromAddr (ρ n) (L.resolvers n)
      (lay (ρ n)).pointer ((0#w).setWidth _)
    refine ⟨.cons (.value S.1) .nil, S.2, List.cons_ne_nil _ _, ?_⟩
    show (ptrFromIntRule lay ρ L n w (.value 0#w) : StateT (Memories _ (unitsOf lay)) SetM _) _ _
    exact (SetM.stateMap_apply _ _ _ _).2 (.inl ⟨_, _, (Fir.fromAddr_apply _ _ _ _ _ _).2 rfl, rfl⟩)

end Fir.Core
