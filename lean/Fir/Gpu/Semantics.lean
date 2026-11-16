import Fir.Gpu.Effects
import Fir.Gpu.Validation
import Fir.Core.MemoryRuns
import Fir.Core.Alloca

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

A question of `gpu` takes no operand, reads, writes and allocates in no
memory, is never UB and never gives poison. So it runs by its rule in the
set monad and keeps the memories, at every naming of its memories: it is
tied to the set monad, as the core's ops that touch no memory are.

`gpu.work_group_alloca` allocates as `alloca` does (the section on stack
allocation), in the memory of its result, with the units and the alignment
that `alloca` would take there (`Core.allocaShape`), but with the kind
`global`, the kind of an allocation that lives for the whole run: no frame
records it, so no call frees it when it returns. One work-item runs at a
time, and a run is the run of one work-item, so its allocation lives from
the op until the run of the kernel ends, whichever function of the device
module ran the op. Each time the op runs it makes a new allocation. How the
work-items of one work-group share one allocation is left for when several
work-items run. It needs memory, so it has no rule in the set monad, as
`alloca` has none, and `gpu` does not lift the set monad: the section on
work-group allocation proves the dialect's obligations with memory.
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

/-- The results of a question: the work-item's answer to it in its
dimension, as a value of its width. -/
def queryResults (q : Query) (d : Dim) (n : Nat) :
    HVector toType (Fir.returnTypes (d := GpuDialect) (Op.query q d n)) :=
  .cons (.value (BitVec.ofNat n (w.answer q d)) : PoisonOr (BitVec n)) .nil

/-- The rules of `gpu` in the set monad: a question gives its results, and
`gpu.work_group_alloca`, which needs memory, has no outcome there, as
`alloca` has none. No op of `gpu` is a terminator, so the interpreter never
asks for an exit; it is written as a return. -/
instance instDialectDenote : DialectDenote GpuDialect SetM where
  denote
    | .query q d n, _ => pure (queryResults q d n)
    | .alloc .., _ => fun _ => False
  exit _ _ := pure .ret

variable {N : Type} {m : Type → Type} [Monad m]

/-- The rule of `gpu.work_group_alloca`, in a monad with the memory effect
on the memories of a run whose layout entries are `lay`, where the run names
`gpu`'s memory `x` as `ρ x`: it allocates the units of `c` values of `t` in
the memory of its result, with the alignment `a` or the type's default one,
as `alloca` does, but of the kind `global`, which lives for the whole run,
and gives the pointer to the allocation. -/
def allocRule (lay : N → MemLayout) (ρ : DialectEffects.Mem GpuDialect → N)
    [MonadMemory N (unitsOf lay) m] (t : Core.Ty) (c : Nat) (a : Option Nat) (n : Nat) :
    m (HVector toType (Fir.returnTypes (d := GpuDialect) (Op.alloc t c a n))) :=
  (fun p => .cons (.value p) .nil) <$>
    MonadMemory.alloc (ρ (.inl n)) .global (Core.allocaShape lay (fun x => ρ (.inl x)) t c a n).1
      (Core.allocaShape lay (fun x => ρ (.inl x)) t c a n).2

/-- The rules of `gpu` in a monad with memory: a question gives its results,
and an allocation allocates. -/
@[reducible] def memDenoteIn (lay : N → MemLayout) (ρ : DialectEffects.Mem GpuDialect → N)
    [MonadMemory N (unitsOf lay) m] : DialectDenote GpuDialect m where
  denote
    | .query q d n, _ => pure (queryResults q d n)
    | .alloc t c a n, _ => allocRule lay ρ t c a n
  exit _ _ := pure .ret

/-- The semantics of `gpu` with memory, at each layout and naming of its
memories: its rules in the state layer over the set monad. -/
instance instDialectMemDenote : DialectMemDenote GpuDialect := ⟨fun lay ρ => memDenoteIn lay ρ⟩

end

/-- No op of `gpu` calls a function. -/
instance instDialectCall : DialectCall GpuDialect := ⟨fun _ => none⟩

variable [WorkItem]

/-- A question of `gpu` gives its results: it never ends in UB and has one
outcome. -/
theorem query_denote_eq (q : Query) (d : Dim) (n : Nat)
    (args : HVector toType (Fir.sig (d := GpuDialect) (Op.query q d n))) (e) :
    DialectDenote.denote (m := SetM) (d := GpuDialect) (Op.query q d n) args e ↔
      e = .ok (queryResults q d n) :=
  Iff.rfl

/-- The results of a question hold no poison. -/
theorem queryResults_noPoison (q : Query) (d : Dim) (n : Nat) :
    ¬ (queryResults q d n).Any TyPoison.IsPoison := by
  rintro (h | h) <;> cases h

/-- The results of a question refine themselves. -/
theorem queryResults_refl (q : Query) (d : Dim) (n : Nat) :
    HVector.Forall₂ TyRefinement.IsRefinedBy (queryResults q d n) (queryResults q d n) :=
  ⟨Core.Ty.isRefinedBy_refl (t := .int _) _, trivial⟩

/-- A question touches no memory: at every layout and naming, it runs with
memory by its rule in the set monad and keeps the memories. -/
theorem query_liftsSetM (q : Query) (d : Dim) (n : Nat) :
    OpLiftsSetM (d := GpuDialect) (Op.query q d n) := fun _ _ _ =>
  ⟨funext fun S => (pure_bind (f := fun a => (pure (a, S) : SetM _)) _).symm,
    funext fun S => (pure_bind (f := fun a => (pure (a, S) : SetM _)) Exit.ret).symm⟩

/-- A question propagates poison: it takes no operand, and never ends in
UB. -/
theorem query_propagates (q : Query) (d : Dim) (n : Nat) :
    PropagatesPoison (d := GpuDialect) (Op.query q d n) where
  poisonOut args h := by cases args; cases h
  ubByOwnRules args _ h := by cases args; cases h

/-- A question is monotone, at every width: it gives the same results
whatever its operands. -/
theorem query_monotone (q : Query) (d : Dim) (n : Nat) :
    OpMonotone (d := GpuDialect) (Op.query q d n) := fun _ _ _ =>
  ⟨fun _ e he => by cases he; exact ⟨_, rfl, queryResults_refl q d n⟩, fun h => by cases h⟩

/-- A question has an outcome on every operand vector. -/
theorem query_total (q : Query) (d : Dim) (n : Nat) : OpTotal (d := GpuDialect) (Op.query q d n) :=
  fun _ => ⟨fun _ => ⟨_, rfl⟩, fun h => by cases h⟩

/-- A question returns a result on the empty, defined operand vector. -/
theorem query_returnsOnDefined (q : Query) (d : Dim) (n : Nat) :
    ReturnsOnDefined (d := GpuDialect) (Op.query q d n) :=
  ⟨.nil, nofun, _, rfl⟩

/-- A question never ends in UB in the set monad. -/
theorem query_neverUBSetM (q : Query) (d : Dim) (n : Nat) :
    NeverUBSetM (d := GpuDialect) (Op.query q d n) := fun _ _ =>
  ⟨fun _ h => (nomatch (query_denote_eq q d n _ _).1 h), fun h => by cases h⟩

/-- A question makes no poison in the set monad. -/
theorem query_makesNoPoisonSetM (q : Query) (d : Dim) (n : Nat) :
    MakesNoPoisonSetM (d := GpuDialect) (Op.query q d n) := fun _ _ _ _ hr => by
  cases hr
  exact queryResults_noPoison q d n

end Fir.Gpu
