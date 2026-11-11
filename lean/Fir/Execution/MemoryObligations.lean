import Fir.Execution.MemoryState
import Fir.Execution.OpEffects

/-!
# Memory obligations

An op that leaves a memory-named effect out of its declaration must not
have it (ADR-2026-11-09-1541). This section says what that means, over an
op's semantics in the state layer, where a computation takes the memories
of a run and gives each way it may end with the memories after it. For a
memory `x` of the run:

* _No write to x_: on each path that ends, every allocation of `x` that was
  there before holds the units it held. New allocations may follow them.
* _No allocation in x_: on each path that ends, `x` has the allocations it
  had, each with its kind, its size and its liveness, and the frames list
  the same stack allocations of `x`. So the op neither allocates nor frees
  in `x`.
* _No read of x_: the op does not depend on the units of `x`. Run it from
  the memories `S`, and from `S` with `x` replaced by any memory of the
  same allocations, each with its kind, size and liveness. Each way the
  first run may end, the second may end too: in UB for the same reason, or
  with the same results and memories that differ only in `x`. There, each
  unit is the same in both, or is in each the unit it was before. A load
  of `x` gives units that differ between the two runs, so it reads `x`.
  A store to `x` writes the same units in both and leaves the rest, so it
  does not read `x`, although whether it faults depends on the allocations
  of `x`.

An op that neither writes nor allocates in `x` leaves `x` as it was.
UB ends a path and shows no memory, so no write and no allocation speak of
the paths that end in results. No read speaks of UB too: from the other
memory, UB comes for the same reason.

A run names its memories, and a dialect names its own: the core's default
memory may be the memory `0` of a run, and a dialect that a sum holds sees
its memories under the sum's names. So a dialect gives its semantics in
the state layer _wherever a run names its memories_: for every type of
names `N` of a run, the unit width of each, and every map `ρ` from the
dialect's memory names to `N`. An op names a memory of the run when its
declaration, with its names mapped by `ρ`, holds it; a declaration of
every memory names each memory of the run. A dialect whose ops touch no
memory runs each op by its rule and keeps the memories, at every naming.
-/

namespace Fir

open Memory

namespace Memory

variable {u : Nat}

/-- The allocations of a memory: the kind, the size and the liveness of
each block, in the order they were made. -/
def Memory.allocs (M : Memory u) : List (AllocKind × Nat × Bool) :=
  M.blocks.map fun b => (b.kind, b.units.length, b.live)

/-- The units of each block of a memory, in the order they were made. -/
def Memory.contents (M : Memory u) : List (List (MemUnit u)) :=
  M.blocks.map (·.units)

/-- The unit at offset `i` of the allocation `a`, if there is one. -/
def Memory.unitAt (M : Memory u) (a : AllocId) (i : Nat) : Option (MemUnit u) :=
  (M.blocks.drop a).head?.bind fun b => (b.units.drop i).head?

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

/-- The stack allocations of the memory `x` that each frame lists, the
innermost frame first. -/
def Memories.framesOf (S : Memories Mem unit) (x : Mem) : List (List AllocId) :=
  S.frames.map fun fr => fr.filterMap fun p => if p.1 = x then some p.2 else none

/-- Two memories of a run agree off `x` when they have the same frames, the
same memory at every name but `x`, and the same allocations in `x`. -/
def Memories.AgreeOff (S₁ S₂ : Memories Mem unit) (x : Mem) : Prop :=
  S₁.frames = S₂.frames ∧ (∀ y, y ≠ x → S₁.mem y = S₂.mem y) ∧
    (S₁.mem x).allocs = (S₂.mem x).allocs

end Memory

/-! # Obligations of a computation -/

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem] {α : Type}

/-- The computation `c` writes no unit of the memory `x`: on each path that
ends, the allocations of `x` that were there before hold the units they
held. -/
def WritesNot (x : Mem) (c : StateT (Memories Mem unit) SetM α) : Prop :=
  ∀ S a S', c S (.ok (a, S')) → (S.mem x).contents <+: (S'.mem x).contents

/-- The computation `c` neither allocates nor frees in the memory `x`: on
each path that ends, `x` has the allocations it had, and the frames list
the same stack allocations of `x`. -/
def AllocatesNot (x : Mem) (c : StateT (Memories Mem unit) SetM α) : Prop :=
  ∀ S a S', c S (.ok (a, S')) →
    (S'.mem x).allocs = (S.mem x).allocs ∧ S'.framesOf x = S.framesOf x

/-- How an outcome of a run from `S` matches one of a run from `S` with the
memory `x` replaced by `m`, for a computation that does not read `x`: UB for
the same reason, or the same results, with memories that agree off `x` and
whose units of `x` are each the same in both or as they were in each. -/
def ReadsNot.Match (x : Mem) (S : Memories Mem unit) (m : Memory (unit x)) :
    Ev (α × Memories Mem unit) → Ev (α × Memories Mem unit) → Prop
  | .ub r, .ub r' => r = r'
  | .ok p₁, .ok p₂ => p₁.1 = p₂.1 ∧ p₁.2.AgreeOff p₂.2 x ∧
    ∀ b i, (p₁.2.mem x).unitAt b i = (p₂.2.mem x).unitAt b i ∨
      ((p₁.2.mem x).unitAt b i = (S.mem x).unitAt b i ∧ (p₂.2.mem x).unitAt b i = m.unitAt b i)
  | .ok _, .ub _ | .ub _, .ok _ => False

/-- The computation `c` does not read the memory `x`: from the memories `S`
with `x` replaced by any memory `m` of the same allocations, each way `c`
may end from `S` has a match. -/
def ReadsNot (x : Mem) (c : StateT (Memories Mem unit) SetM α) : Prop :=
  ∀ S (m : Memory (unit x)), m.allocs = (S.mem x).allocs →
    ∀ e, c S e → ∃ e', c (S.set x m) e' ∧ ReadsNot.Match x S m e e'

/-! # A dialect's semantics with memory -/

/-- A dialect's semantics in the state layer over the set monad, wherever a
run names its memories: for the names `N` of a run's memories, the unit
width of each, and the name `ρ x` that the run gives each memory `x` of the
dialect. -/
class DialectMemDenote (d : Dialect) [TyDenote d.Ty] [DialectSignature d] [DialectEffects d] where
  /-- The semantics of each op, where the run names the dialect's memory `x`
  as `ρ x`. -/
  denoteAt : {N : Type} → [DecidableEq N] → (unit : N → Nat) → (ρ : DialectEffects.Mem d → N) →
    DialectDenote d (StateT (Memories N unit) SetM)

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectEffects d]
  [DialectMemDenote d]

/-- What an op runs by its own rule, where a run names the dialect's
memories by `ρ`, has the property `P`: the op's meaning when it is not a
terminator, and its exit when it is. -/
def OwnRuleHas {N : Type} [DecidableEq N] (unit : N → Nat) (ρ : DialectEffects.Mem d → N)
    (P : {α : Type} → StateT (Memories N unit) SetM α → Prop) (op : d.Op) : Prop :=
  letI := DialectMemDenote.denoteAt (d := d) unit ρ
  ∀ args : HVector toType (sig op),
    (isTerminator op = false → P (DialectDenote.denote op args)) ∧
    (isTerminator op = true → P (DialectDenote.exit op args))

end Fir
