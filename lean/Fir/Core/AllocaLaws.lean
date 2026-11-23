import Fir.Core.MemRules
import Fir.Execution.MemoryAllocLaws
import Fir.Execution.MemoryPoison

/-!
# Stack allocation obligations

`alloca` touches memory, so it has no rule in the set monad and no tie to
it: it meets each obligation with memory by its own rule, wherever a run
names the core's memories and whatever their layout entries. Its rule
allocates in the memory of its result and gives the pointer, and the
allocation in the state layer has one outcome from any memories (the
section on allocation in the state layer). So:

* _Effects._ It never ends in UB, and its result, a pointer, is never
  poison. It writes no unit of any memory and reads none, and it allocates
  in no memory but the one it declares, the memory of its result.
* _Totality._ It has an outcome from any memories.
* _Monotonicity._ From memories that refine others, it allocates at the
  same place, so it gives the same pointer and memories that refine the
  others'.
* _Poison with memory._ It has no operands, so a poison operand is never
  there to give poison or UB, and it gives a result from memories inside a
  call.
* _Finitely many outcomes._ It has one, from any memories.

The frame of its call frees a stack allocation when the call returns, which
the section on the memories of a run proves of every stack allocation.
-/

namespace Fir.Core

open Memory

variable (k : AllocKind) (t : Ty) (c : Nat) (a : Option Nat) (n : Nat)

/-- A property holds of every core op when it holds of each op that
touches no memory and reads no item of the run, of `alloca`, of `load`, of
`store`, of `loadPtr`, of `storePtr`, of `loadFloat`, of `storeFloat`, of
`fieldAddr`, of `globalAddr`, of `memCopy`, of `memSet`, of `ptrExpose` and
of `ptrFromInt`. So an obligation with memory is met op by op:
by its tie for the first, and by its own rule for each op that touches
memory or reads the run's items. -/
theorem Op.memCases {P : Op → Prop} (op : Op)
    (ht : ∀ op, op.touchesMemory = false → op.readsItems = false → P op)
    (ha : ∀ k t c a n, P (.alloca k t c a n)) (hl : ∀ o w a n, P (.load o w a n))
    (hs : ∀ o w a n, P (.store o w a n)) (hlp : ∀ o mp a n, P (.loadPtr o mp a n))
    (hsp : ∀ o mp a n, P (.storePtr o mp a n)) (hlf : ∀ o e m a n, P (.loadFloat o e m a n))
    (hsf : ∀ o e m a n, P (.storeFloat o e m a n)) (hf : ∀ s j n w, P (.fieldAddr s j n w))
    (hg : ∀ s n, P (.globalAddr s n)) (hfa : ∀ s n, P (.funcAddr s n))
    (hmc : ∀ k o w n, P (.memCopy k o w n)) (hms : ∀ o v w n, P (.memSet o v w n))
    (hexp : ∀ n w, P (.ptrExpose n w)) (hfrom : ∀ n w, P (.ptrFromInt n w)) :
    P op := by
  cases hm : op.touchesMemory
  · cases hi : op.readsItems
    · exact ht op hm hi
    · cases op <;> first | exact hf .. | exact hg .. | exact hfa .. | cases hi
  · cases op <;> first
      | exact ha .. | exact hl .. | exact hs .. | exact hlp .. | exact hsp .. | exact hlf ..
      | exact hsf .. | exact hmc .. | exact hms .. | exact hexp .. | exact hfrom .. | cases hm

/-- A core op with an outcome in the set monad touches no memory: `alloca`,
the loads and stores, `load`, `store`, `loadPtr`, `storePtr`,
`loadFloat` and `storeFloat`, `memCopy`, `memSet`, `ptrExpose` and
`ptrFromInt` have none there. -/
theorem Op.touchesMemory_false_of_denote {op : Op}
    {args : HVector toType (Fir.sig (d := CoreDialect) op)}
    {e : Ev (HVector toType (Fir.returnTypes (d := CoreDialect) op))}
    (h : DialectDenote.denote (m := SetM) (d := CoreDialect) op args e) :
    op.touchesMemory = false := by
  cases op with
  | alloca | load | store | loadPtr | storePtr | loadFloat | storeFloat | memCopy | memSet
  | ptrExpose | ptrFromInt => exact h.elim
  | _ => rfl

/-- A core op with an outcome in the set monad reads no item of the run:
`fieldAddr`, `globalAddr` and `funcAddr` have none there. -/
theorem Op.readsItems_false_of_denote {op : Op}
    {args : HVector toType (Fir.sig (d := CoreDialect) op)}
    {e : Ev (HVector toType (Fir.returnTypes (d := CoreDialect) op))}
    (h : DialectDenote.denote (m := SetM) (d := CoreDialect) op args e) :
    op.readsItems = false := by
  cases op with
  | fieldAddr | globalAddr | funcAddr => exact h.elim
  | _ => rfl

/-- The result vector of `alloca`, from the pointer it allocates. -/
abbrev allocaResult (n : Nat) (p : Pointer) : HVector toType [Ty.ptr n] := .cons (.value p) .nil

section

variable {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : Mem → N) (L : RunItems)

/-- The allocation that `alloca`'s rule makes, in the state layer over the
set monad. -/
abbrev allocaAlloc : StateT (Memories N (unitsOf lay)) SetM Pointer :=
  MonadMemory.alloc (ρ n) k (allocaShape lay ρ t c a n).1 (allocaShape lay ρ t c a n).2

/-- `alloca` runs with memory by its rule: its allocation, with the pointer
as its result. -/
theorem alloca_denote (args : HVector toType (Fir.sig (d := CoreDialect) (Op.alloca k t c a n))) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L
    @Eq (StateT (Memories N (unitsOf lay)) SetM (HVector toType [Ty.ptr n]))
      (DialectDenote.denote (d := CoreDialect) (m := StateT (Memories N (unitsOf lay)) SetM)
        (Op.alloca k t c a n) args)
      (allocaResult n <$> allocaAlloc k t c a n lay ρ) :=
  rfl

end

/-- `alloca` never ends in UB. -/
theorem alloca_neverUB : NeverUB (d := CoreDialect) (.alloca k t c a n) := fun lay _ _ _ =>
  ⟨fun _ => (alloc_noUB (unit := unitsOf lay) _ _ _ _).map (allocaResult n),
    fun h => nomatch h⟩

/-- `alloca` gives a pointer, never poison. -/
theorem alloca_makesNoPoison : MakesNoPoison (d := CoreDialect) (.alloca k t c a n) := by
  intro _ N _ lay ρ L args _ S rs S' h
  rw [alloca_denote] at h
  rcases (SetM.stateMap_apply _ _ S _).1 h with ⟨p, _, _, he⟩ | ⟨_, _, he⟩ <;> cases he
  exact fun h => by rcases h with h | h <;> cases h

/-- `alloca` writes no unit of any memory. -/
theorem alloca_writesNot {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : Mem → N) (L :
    RunItems) (x : N) :
    OwnRuleHas lay ρ L (WritesNot x) (d := CoreDialect) (.alloca k t c a n) := fun _ =>
  ⟨fun _ => (alloc_writesNot (unit := unitsOf lay) _ _ _ _ x).map (allocaResult n),
    fun h => nomatch h⟩

/-- `alloca` reads no memory. -/
theorem alloca_readsNot {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : Mem → N) (L :
    RunItems) (x : N) :
    OwnRuleHas lay ρ L (ReadsNot x) (d := CoreDialect) (.alloca k t c a n) := fun _ =>
  ⟨fun _ => (alloc_readsNot (unit := unitsOf lay) _ _ _ _ x).map (allocaResult n),
    fun h => nomatch h⟩

/-- `alloca` allocates in no memory but the memory of its result. -/
theorem alloca_allocatesNot {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : Mem → N) (L :
    RunItems) (x : N)
    (hx : ¬ ((Fir.effects (d := CoreDialect) (.alloca k t c a n)).allocates.map ρ).Has x) :
    OwnRuleHas lay ρ L (AllocatesNot x) (d := CoreDialect) (.alloca k t c a n) := fun _ =>
  ⟨fun _ => (alloc_allocatesNot (unit := unitsOf lay) _ _ _ _
      fun h => hx (List.mem_singleton.2 h.symm)).map (allocaResult n),
    fun h => nomatch h⟩

/-- `alloca` has an outcome from any memories. -/
theorem alloca_memTotal : MemTotal (d := CoreDialect) (.alloca k t c a n) := fun lay _ _ _ =>
  ⟨fun _ => (alloc_hasOutcome (unit := unitsOf lay) _ _ _ _).map (allocaResult n),
    fun h => nomatch h⟩

/-- From memories that refine others, `alloca` gives the same pointer and
memories that refine the others'. -/
theorem alloca_memMonotone : MemMonotone (d := CoreDialect) (.alloca k t c a n) :=
  fun lay _ _ _ _ _ =>
    ⟨fun _ => StateRefinedBy.map (allocaResult n)
        (fun {p p'} (h : p = p') => by subst h; exact ⟨Ty.isRefinedBy_refl _, trivial⟩)
        (alloc_refines (unit := unitsOf lay) _ _ _ _),
      fun h => nomatch h⟩

/-- `alloca` has no operands, so it propagates poison with memory. -/
theorem alloca_memPropagates : MemPropagatesPoison (d := CoreDialect) (.alloca k t c a n) where
  poisonOut _ _ _ args h := by cases args with | nil => exact h.elim
  ubByOwnRules _ _ _ args _ _ h := by cases args with | nil => exact h.elim

/-- `alloca` gives a result from memories inside a call. -/
theorem alloca_memReturnsOnDefined :
    MemReturnsOnDefined (d := CoreDialect) (.alloca k t c a n) := fun lay ρ L => by
  let S : Memories _ (unitsOf lay) := Memories.empty.enter
  let q := S.alloc (ρ n) k (allocaShape lay ρ t c a n).1 (allocaShape lay ρ t c a n).2
  refine ⟨.nil, fun h => h, S, allocaResult n q.1, q.2, List.cons_ne_nil _ _, ?_⟩
  exact (SetM.stateMap_apply (allocaResult n) (allocaAlloc k t c a n lay ρ) _ _).2
    (.inl ⟨q.1, q.2, rfl, rfl⟩)

/-- `alloca` has one outcome from any memories. -/
theorem alloca_finitelyMany {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : Mem → N) (L :
    RunItems)
    (args : HVector toType (Fir.sig (d := CoreDialect) (Op.alloca k t c a n))) :
    letI := DialectMemDenote.denoteAt (d := CoreDialect) lay ρ L
    FinitelyMany (DialectDenote.denote (d := CoreDialect)
      (m := StateT (Memories N (unitsOf lay)) SetM) (Op.alloca k t c a n) args) := fun S => by
  obtain ⟨L, hL⟩ := alloc_finitelyMany (unit := unitsOf lay) (ρ n) k
    (allocaShape lay ρ t c a n).1 (allocaShape lay ρ t c a n).2 S
  refine ⟨L.map fun q => (allocaResult n q.1, q.2), fun x hx => ?_⟩
  rw [alloca_denote] at hx
  rcases (SetM.stateMap_apply _ _ S _).1 hx with ⟨p, S', hp, he⟩ | ⟨_, _, he⟩ <;> cases he
  exact List.mem_map.2 ⟨(p, S'), hL _ hp, rfl⟩

end Fir.Core
