import Fir.Gpu.Semantics
import Fir.Core.AllocaLaws

/-!
# Work-group allocation obligations

`gpu.work_group_alloca` touches memory, so it has no rule in the set monad
and no tie to it: it meets each obligation with memory by its own rule,
wherever a run names `gpu`'s memories and whatever their layout entries, as
`alloca` does (the section on the stack allocation obligations). Its rule
allocates in the memory of its result, of the kind `global`, and gives the
pointer, and the allocation in the state layer has one outcome from any
memories, whatever its kind. So:

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

A question is tied to the set monad, and meets each obligation by its tie
and what it meets there. So `gpu` meets every obligation of its classes
with memory, at every work-item: its effect set is sound
(`Gpu.lawfulDialectEffects`), and it is lawful in its totality, its
monotonicity and its poison with memory.
-/

namespace Fir.Gpu

open Memory

variable [WorkItem] (t : Core.Ty) (c : Nat) (a : Option Nat) (n : Nat)

omit [WorkItem] in
/-- A property holds of every op of `gpu` when it holds of each question and
of each allocation. -/
theorem Op.memCases {P : Op → Prop} (op : Op) (hq : ∀ q d w, P (.query q d w))
    (ha : ∀ t c a n, P (.alloc t c a n)) : P op := by
  cases op
  · exact hq ..
  · exact ha ..

/-- The result vector of an allocation, from the pointer it allocates. -/
abbrev allocResult (p : Pointer) : HVector toType (Fir.returnTypes (d := GpuDialect) (Op.alloc t c a n)) :=
  .cons (.value p) .nil

section

variable {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem GpuDialect → N)
    (L : RunItems)

/-- The allocation that `gpu.work_group_alloca`'s rule makes, in the state
layer over the set monad. -/
abbrev allocAlloc : StateT (Memories N (unitsOf lay)) SetM Pointer :=
  Core.allocaAlloc .global t c a n lay (fun x => ρ (.inl x))

/-- `gpu.work_group_alloca` runs with memory by its rule: its allocation,
with the pointer as its result. -/
theorem alloc_denote (args : HVector toType (Fir.sig (d := GpuDialect) (Op.alloc t c a n))) :
    letI := DialectMemDenote.denoteAt (d := GpuDialect) lay ρ L
    @Eq (StateT (Memories N (unitsOf lay)) SetM _)
      (DialectDenote.denote (d := GpuDialect) (m := StateT (Memories N (unitsOf lay)) SetM)
        (Op.alloc t c a n) args)
      (allocResult t c a n <$> allocAlloc t c a n lay ρ) :=
  rfl

end

/-- `gpu.work_group_alloca` never ends in UB. -/
theorem Op.alloc_neverUB : NeverUB (d := GpuDialect) (.alloc t c a n) := fun lay _ _ _ =>
  ⟨fun _ => (Fir.alloc_noUB (unit := unitsOf lay) _ _ _ _).map (allocResult t c a n),
    fun h => nomatch h⟩

/-- `gpu.work_group_alloca` gives a pointer, never poison. -/
theorem Op.alloc_makesNoPoison : MakesNoPoison (d := GpuDialect) (.alloc t c a n) := by
  intro _ N _ lay ρ L args _ S rs S' h
  rw [alloc_denote] at h
  rcases (SetM.stateMap_apply _ _ S _).1 h with ⟨p, _, _, he⟩ | ⟨_, _, he⟩ <;> cases he
  exact fun h => by rcases h with h | h <;> cases h

/-- `gpu.work_group_alloca` writes no unit of any memory. -/
theorem Op.alloc_writesNot {N : Type} [DecidableEq N] (lay : N → MemLayout)
    (ρ : DialectEffects.Mem GpuDialect → N) (L : RunItems) (x : N) :
    OwnRuleHas lay ρ L (WritesNot x) (d := GpuDialect) (.alloc t c a n) := fun _ =>
  ⟨fun _ => (Fir.alloc_writesNot (unit := unitsOf lay) _ _ _ _ x).map (allocResult t c a n),
    fun h => nomatch h⟩

/-- `gpu.work_group_alloca` reads no memory. -/
theorem Op.alloc_readsNot {N : Type} [DecidableEq N] (lay : N → MemLayout)
    (ρ : DialectEffects.Mem GpuDialect → N) (L : RunItems) (x : N) :
    OwnRuleHas lay ρ L (ReadsNot x) (d := GpuDialect) (.alloc t c a n) := fun _ =>
  ⟨fun _ => (Fir.alloc_readsNot (unit := unitsOf lay) _ _ _ _ x).map (allocResult t c a n),
    fun h => nomatch h⟩

/-- `gpu.work_group_alloca` allocates in no memory but the memory of its
result. -/
theorem Op.alloc_allocatesNot {N : Type} [DecidableEq N] (lay : N → MemLayout)
    (ρ : DialectEffects.Mem GpuDialect → N) (L : RunItems) (x : N)
    (hx : ¬ ((Fir.effects (d := GpuDialect) (.alloc t c a n)).allocates.map ρ).Has x) :
    OwnRuleHas lay ρ L (AllocatesNot x) (d := GpuDialect) (.alloc t c a n) := fun _ =>
  ⟨fun _ => (Fir.alloc_allocatesNot (unit := unitsOf lay) _ _ _ _
      fun h => hx (List.mem_singleton.2 h.symm)).map (allocResult t c a n),
    fun h => nomatch h⟩

/-- `gpu.work_group_alloca` has an outcome from any memories. -/
theorem Op.alloc_memTotal : MemTotal (d := GpuDialect) (.alloc t c a n) := fun lay _ _ _ =>
  ⟨fun _ => (Fir.alloc_hasOutcome (unit := unitsOf lay) _ _ _ _).map (allocResult t c a n),
    fun h => nomatch h⟩

/-- From memories that refine others, `gpu.work_group_alloca` gives the
same pointer and memories that refine the others'. -/
theorem Op.alloc_memMonotone : MemMonotone (d := GpuDialect) (.alloc t c a n) :=
  fun lay _ _ _ _ _ =>
    ⟨fun _ => StateRefinedBy.map (allocResult t c a n)
        (fun {p p'} (h : p = p') => by subst h; exact ⟨Core.Ty.isRefinedBy_refl (t := .ptr n) _, trivial⟩)
        (Fir.alloc_refines (unit := unitsOf lay) _ _ _ _),
      fun h => nomatch h⟩

/-- `gpu.work_group_alloca` has no operands, so it propagates poison with
memory. -/
theorem Op.alloc_memPropagates : MemPropagatesPoison (d := GpuDialect) (.alloc t c a n) where
  poisonOut _ _ _ args h := by cases args with | nil => exact h.elim
  ubByOwnRules _ _ _ args _ _ h := by cases args with | nil => exact h.elim

/-- `gpu.work_group_alloca` gives a result from memories inside a call. -/
theorem Op.alloc_memReturnsOnDefined :
    MemReturnsOnDefined (d := GpuDialect) (.alloc t c a n) := fun lay ρ L => by
  let S : Memories _ (unitsOf lay) := Memories.empty.enter
  let sh := Core.allocaShape lay (fun x => ρ (.inl x)) t c a n
  let q := S.alloc (ρ (.inl n)) .global sh.1 sh.2
  refine ⟨.nil, fun h => h, S, allocResult t c a n q.1, q.2, List.cons_ne_nil _ _, ?_⟩
  exact (SetM.stateMap_apply (allocResult t c a n) (allocAlloc t c a n lay ρ) _ _).2
    (.inl ⟨q.1, q.2, rfl, rfl⟩)

/-- `gpu.work_group_alloca` has one outcome from any memories. -/
theorem Op.alloc_finitelyMany {N : Type} [DecidableEq N] (lay : N → MemLayout)
    (ρ : DialectEffects.Mem GpuDialect → N) (L : RunItems)
    (args : HVector toType (Fir.sig (d := GpuDialect) (Op.alloc t c a n))) :
    letI := DialectMemDenote.denoteAt (d := GpuDialect) lay ρ L
    FinitelyMany (DialectDenote.denote (d := GpuDialect)
      (m := StateT (Memories N (unitsOf lay)) SetM) (Op.alloc t c a n) args) := fun S => by
  let sh := Core.allocaShape lay (fun x => ρ (.inl x)) t c a n
  obtain ⟨L, hL⟩ := Fir.alloc_finitelyMany (unit := unitsOf lay) (ρ (.inl n)) .global sh.1 sh.2 S
  refine ⟨L.map fun q => (allocResult t c a n q.1, q.2), fun x hx => ?_⟩
  rw [alloc_denote] at hx
  rcases (SetM.stateMap_apply _ _ S _).1 hx with ⟨p, S', hp, he⟩ | ⟨_, _, he⟩ <;> cases he
  exact List.mem_map.2 ⟨(p, S'), hL _ hp, rfl⟩

/-! # The obligations of the dialect -/

/-- The effect set of `gpu` is sound at every work-item: a question, whose
set is empty, is tied, never ends in UB, gives no poison, and writes, reads
and allocates in no memory; `gpu.work_group_alloca` allocates in the memory
of its result alone; and no op is a terminator. -/
instance lawfulDialectEffects : LawfulDialectEffects GpuDialect where
  neverUB op _ _ _ := Op.memCases (P := fun op => NeverUB (d := GpuDialect) op) op
    (fun q d w => NeverUB.ofLifts (query_liftsSetM q d w) (query_neverUBSetM q d w))
    Op.alloc_neverUB
  makesNoPoison op _ _ _ := Op.memCases (P := fun op => MakesNoPoison (d := GpuDialect) op) op
    (fun q d w => MakesNoPoison.ofLifts (query_liftsSetM q d w) (query_makesNoPoisonSetM q d w))
    Op.alloc_makesNoPoison
  notControl op _ := by cases op <;> rfl
  writesNot op _ _ _ _ lay ρ L x _ := Op.memCases
    (P := fun op => OwnRuleHas lay ρ L (WritesNot x) (d := GpuDialect) op) op
    (fun q d w => OwnRuleHas.ofLifts (query_liftsSetM q d w) lay ρ L fun c => writesNot_lift x c)
    fun t c a n => Op.alloc_writesNot t c a n lay ρ L x
  readsNot op _ _ _ _ lay ρ L x _ := Op.memCases
    (P := fun op => OwnRuleHas lay ρ L (ReadsNot x) (d := GpuDialect) op) op
    (fun q d w => OwnRuleHas.ofLifts (query_liftsSetM q d w) lay ρ L fun c => readsNot_lift x c)
    fun t c a n => Op.alloc_readsNot t c a n lay ρ L x
  allocatesNot op _ _ _ _ lay ρ L x hx := by
    cases op with
    | query q d w =>
      exact OwnRuleHas.ofLifts (query_liftsSetM q d w) lay ρ L fun c => allocatesNot_lift x c
    | alloc t c a n => exact Op.alloc_allocatesNot t c a n lay ρ L x hx

/-- `gpu` is lawful in its totality: a question is total and tied, and an
allocation has an outcome from any memories. -/
instance lawfulTotal : LawfulDialectTotal GpuDialect :=
  ⟨fun op _ _ => Op.memCases (P := fun op => MemTotal (d := GpuDialect) op) op
    (fun q d w => MemTotal.ofLifts (query_liftsSetM q d w) (query_total q d w)) Op.alloc_memTotal⟩

/-- Every op of `gpu` is monotone with memory, at every width, valid or
not. -/
theorem Op.memMonotone (op : Op) : MemMonotone (d := GpuDialect) op :=
  Op.memCases (P := fun op => MemMonotone (d := GpuDialect) op) op
    (fun q d w => MemMonotone.ofLifts (query_liftsSetM q d w) (query_monotone q d w))
    Op.alloc_memMonotone

/-- `gpu` is lawful in its monotonicity. -/
instance lawfulMonotone : LawfulDialectMonotone GpuDialect := ⟨fun op _ _ => Op.memMonotone op⟩

/-- `gpu` is lawful in its poison with memory: a poison value of a core
type is refined by every value of its type, and each op propagates poison
and returns a result on the empty, defined operand vector. -/
instance lawfulMemPoison : LawfulDialectMemPoison GpuDialect where
  poison_isRefinedBy {t} := match t with
    | .inl _ => fun _ => Core.Ty.poison_isRefinedBy
    | .inr e => e.elim
  propagates op _ _ := Op.memCases (P := fun op => MemPropagatesPoison (d := GpuDialect) op) op
    (fun q d w => MemPropagatesPoison.ofLifts (query_liftsSetM q d w) (query_propagates q d w))
    Op.alloc_memPropagates
  returnsOnDefined op _ _ := Op.memCases (P := fun op => MemReturnsOnDefined (d := GpuDialect) op) op
    (fun q d w => MemReturnsOnDefined.ofLifts (query_liftsSetM q d w) (query_returnsOnDefined q d w))
    Op.alloc_memReturnsOnDefined

end Fir.Gpu
