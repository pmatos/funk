import Fir.Gpu.Effects
import Fir.Gpu.Validation
import Fir.Core.MemoryRuns

/-!
The rules of `gpu` (ADR-2026-11-09-1545). In M1 a kernel runs one
work-item at a time, and the work-item is the run's input, as its
arguments are: its id within its work-group, its work-group's id, the
number of work-items in a work-group and the number of work-groups, in
each of the three dimensions. They are fixed for the whole run. An op of
`gpu` gives one of them: `gpu.work_item_id gpu.x` gives the work-item's id
in the dimension `gpu.x`, as an `iN` of the op's width, the number taken
modulo 2 to the power `N`. Validation asks for an `i32`. A work-item of
its grid (`WorkItem.Valid`) has each id below its size and each number below
2 to the power 32, and is what `fir-ref run` takes.

An op of `gpu` takes no operand, reads, writes and allocates in no memory,
is never UB and never gives poison. So it runs by its rule in the set monad
and keeps the memories, at every naming of its memories, and the dialect
meets every obligation of its classes, at every work-item: it is lawful,
its empty effect set is sound (`Gpu.lawfulDialectEffects`), and it is
lawful in its totality, its monotonicity and its poison with memory.
-/

namespace Fir.Gpu

/-- The work-item that a run runs: in each dimension, its id within its
work-group, its work-group's id, the number of work-items in a work-group
and the number of work-groups. A run takes it as its input, and every op of
`gpu` asks it one question. -/
class WorkItem where
  itemId : Dim → Nat
  groupId : Dim → Nat
  groupSize : Dim → Nat
  numGroups : Dim → Nat

/-- The answer of the work-item to a question in a dimension. -/
def WorkItem.answer (w : WorkItem) : Query → Dim → Nat
  | .workItemId => w.itemId
  | .workGroupId => w.groupId
  | .workGroupSize => w.groupSize
  | .numWorkGroups => w.numGroups

/-- A work-item of its grid: in each dimension, its id is below the size of
its work-group, its work-group's id is below the number of work-groups,
and each number is below 2 to the power 32, so it is an `i32`'s unsigned
value. -/
def WorkItem.Valid (w : WorkItem) : Prop :=
  ∀ d ∈ [Dim.x, .y, .z], w.itemId d < w.groupSize d ∧ w.groupId d < w.numGroups d ∧
    w.groupSize d < 2 ^ 32 ∧ w.numGroups d < 2 ^ 32

instance instDecidableValid (w : WorkItem) : Decidable w.Valid := by
  unfold WorkItem.Valid
  infer_instance

/-- The one work-item of a grid of one work-group of one work-item: every id
`0`, every size `1`. -/
@[instance_reducible] def WorkItem.single : WorkItem := ⟨fun _ => 0, fun _ => 0, fun _ => 1, fun _ => 1⟩

theorem WorkItem.single_valid : WorkItem.single.Valid := by decide

section

variable [w : WorkItem]

/-- The results of an op of `gpu`: the work-item's answer to its question
in its dimension, as a value of its width. -/
def Op.results : (op : Op) → HVector toType (Fir.returnTypes (d := GpuDialect) op)
  | .query q d n => .cons (.value (BitVec.ofNat n (w.answer q d)) : PoisonOr (BitVec n)) .nil

/-- The rules of `gpu` in any monad: an op gives its results. No op of
`gpu` is a terminator, so the interpreter never asks for an exit; it is
written as a return. -/
@[reducible] def denoteIn (m : Type → Type) [Monad m] : DialectDenote GpuDialect m where
  denote op _ := pure op.results
  exit _ _ := pure .ret

/-- The rules of `gpu` in the set monad. -/
instance instDialectDenote : DialectDenote GpuDialect SetM := denoteIn SetM

/-- No op of `gpu` touches memory: at every naming of its memories, it runs
by its rule in the set monad and keeps the memories. -/
instance instDialectMemDenote : DialectMemDenote GpuDialect := DialectMemDenote.ofSetM

/-- The semantics of `gpu` with memory lifts its semantics in the set
monad. -/
instance instLiftsSetM : LiftsSetM GpuDialect := DialectMemDenote.ofSetM_liftsSetM

end

/-- No op of `gpu` calls a function. -/
instance instDialectCall : DialectCall GpuDialect := ⟨fun _ => none⟩

variable [WorkItem]

/-- An op of `gpu` gives its results: it never ends in UB and has one
outcome. -/
theorem denote_eq (op : Op) (args : HVector toType (Fir.sig (d := GpuDialect) op)) (e) :
    DialectDenote.denote (m := SetM) (d := GpuDialect) op args e ↔ e = .ok op.results :=
  Iff.rfl

/-- The results of an op of `gpu` hold no poison. -/
theorem results_noPoison (op : Op) : ¬ op.results.Any TyPoison.IsPoison := by
  cases op
  rintro (h | h) <;> cases h

/-- The results of an op of `gpu` refine themselves. -/
theorem results_refl (op : Op) :
    HVector.Forall₂ TyRefinement.IsRefinedBy op.results op.results := by
  cases op
  exact ⟨Core.Ty.isRefinedBy_refl (t := .int _) _, trivial⟩

/-- Each op of `gpu` propagates poison: it takes no operand, and never ends
in UB. -/
theorem propagates (op : Op) : PropagatesPoison (d := GpuDialect) op where
  poisonOut args h := by cases op; cases args; cases h
  ubByOwnRules args _ h := by cases op; cases args; cases h

/-- Each op of `gpu` is monotone, at every width: it gives the same results
whatever its operands. -/
theorem Op.monotone (op : Op) : OpMonotone (d := GpuDialect) op := fun _ _ _ =>
  ⟨fun _ e he => by cases he; exact ⟨_, rfl, results_refl op⟩, fun h => by cases op; cases h⟩

/-- `gpu` is lawful, at every work-item: each op propagates poison, returns
a result, and is total and monotone. -/
instance lawful : LawfulDialectPoison GpuDialect where
  poison_isRefinedBy {t} := match t with
    | .inl _ => fun _ => Core.Ty.poison_isRefinedBy
    | .inr e => e.elim
  propagates op _ _ := propagates op
  returnsOnDefined op _ _ := by
    cases op
    exact ⟨.nil, nofun, _, rfl⟩
  total op _ _ args := ⟨fun _ => ⟨_, rfl⟩, fun h => by cases op; cases h⟩
  monotone op _ _ := Op.monotone op

/-- The effect set of `gpu`, empty, is sound at every work-item: no op ends
in UB, gives poison, or writes, reads or allocates in a memory, and no op
is a terminator. -/
instance lawfulDialectEffects : LawfulDialectEffects GpuDialect where
  neverUB op _ _ _ := NeverUB.ofSetM fun _ _ =>
    ⟨fun _ h => (nomatch (denote_eq op _ _).1 h), fun h => by cases op; cases h⟩
  makesNoPoison op _ _ _ := MakesNoPoison.ofSetM fun _ _ _ _ hr => by
    cases hr
    exact results_noPoison op
  notControl op _ := by cases op; rfl
  writesNot := DialectMemDenote.ofSetM_writesNot
  readsNot := DialectMemDenote.ofSetM_readsNot
  allocatesNot := DialectMemDenote.ofSetM_allocatesNot

/-- `gpu` is lawful in its totality: it is lawful, and it lifts the set
monad. -/
instance lawfulTotal : LawfulDialectTotal GpuDialect := LawfulDialectTotal.ofLawful

/-- `gpu` is lawful in its monotonicity. -/
instance lawfulMonotone : LawfulDialectMonotone GpuDialect := LawfulDialectMonotone.ofLawful

/-- `gpu` is lawful in its poison with memory. -/
instance lawfulMemPoison : LawfulDialectMemPoison GpuDialect := LawfulDialectMemPoison.ofLawful

end Fir.Gpu
