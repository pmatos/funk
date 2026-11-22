import Fir.Execution.TraceObligations
import Fir.Execution.Observe

/-!
# What the world sees

An event hands values and memory to the world outside the program, which
names an allocation only by its handle (`Fir.Execution.TraceWorld`). So an
event shows each value and each unit as the world sees it, from the traced
state it is shown in:

* a pointer with no provenance is itself;
* a pointer into an escaped live allocation names it by its handle, in
  place of its id;
* any other pointer is poison: it points into an allocation that the world
  cannot name, such as a dangling one, which is poison in the comparison of
  two runs (ADR-2026-11-09-1540; the human's rulings of 2026-11-15 on #309
  and #233).

A unit is seen as the world writes one (`WUnit`): its bits, poison, or a
fragment of a pointer as the world sees it. The world sees the units of
each escaped allocation, by handle, while it is live, and none of one that
is not. An external call shows them after it has let escape what it
reaches, so the world sees every allocation that it can reach (the human's
ruling of 2026-11-20 on #239).

What the world sees is refined as values are: a poison unit by any unit.
Traced states that refine each other let the same allocations escape, in
the same order, and agree on which are live, so they show each pointer
alike, and units and values that refine others as units and values that
refine the others.
-/

namespace Fir

open Memory

/-! # Units the world sees, refined -/

/-- A unit the world sees is refined by itself, and poison by any unit. -/
def WUnit.IsRefinedBy : WUnit → WUnit → Prop
  | .poison, _ => True
  | u, u' => u' = u

instance : HRefinement WUnit WUnit := ⟨WUnit.IsRefinedBy⟩

/-- Refinement of the units the world sees is reflexive. -/
theorem WUnit.isRefinedBy_refl : ∀ u : WUnit, u ⊑ u
  | .poison => trivial
  | .bits _ | .frag .. => rfl

/-- Refinement of the units the world sees is transitive. -/
theorem WUnit.isRefinedBy_trans : ∀ {u v w : WUnit}, u ⊑ v → v ⊑ w → u ⊑ w
  | .poison, _, _, _, _ => trivial
  | .bits _, _, _, rfl, h | .frag .., _, _, rfl, h => h

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

/-! # The world's view -/

/-- The renaming of each escaped allocation of the traced state `s` to its
handle. -/
def TraceState.handles (s : TraceState Mem unit) : Renaming Mem :=
  fun x a => s.escaped.idxOf? (x, a)

/-- The pointer `p` of the memory numbered `n` as the world sees it from the
traced state `s`, where the memory numbered `n` is `μ n`: as an observer
sees it under the renaming of each escaped allocation to its handle
(`Renaming.ptr`), so itself when it has no provenance, the handle of its
allocation in place of the allocation's id when that allocation escaped
and is not freed, and poison (`none`) otherwise. -/
def TraceState.worldPtr (μ : Nat → Mem) (s : TraceState Mem unit) : Nat → Pointer → Option Pointer :=
  Renaming.ptr μ s.mem s.handles

/-- A value as the world sees it from the traced state `s`: each of its
pointers as the world sees it. -/
def TraceState.worldVal {V : Type} [HRefinement V V] [HasPtrs V] (μ : Nat → Mem)
    (s : TraceState Mem unit) (v : V) : V :=
  HasPtrs.map (s.worldPtr μ) v

/-- A unit as the world sees it from the traced state `s`: its bits, poison,
or the fragment of a pointer as the world sees it, which is poison when the
world sees the pointer as poison. -/
def TraceState.worldUnit (μ : Nat → Mem) (s : TraceState Mem unit) {u : Nat} : MemUnit u → WUnit
  | .bits b => .bits b.toNat
  | .poison => .poison
  | .frag m p i => match s.worldPtr μ m p with
    | some q => .frag m q.prov q.offset i
    | none => .poison

/-- The units of each escaped allocation of the traced state `s`, in the
order of their handles, as the world sees them: none of an allocation that
is not live. -/
def TraceState.seen (μ : Nat → Mem) (s : TraceState Mem unit) : List (List WUnit) :=
  s.escaped.map fun (x, a) => match (s.mem.mem x).blocks[a]? with
    | some b => if b.live then b.units.map (s.worldUnit μ) else []
    | none => []

/-! # Refined traced states show refined views -/

/-- Memories that refine each other agree on which allocations are freed. -/
theorem Memory.Memories.freed_eq {S S' : Memories Mem unit} (h : S ⊑ S') (x : Mem)
    (a : AllocId) : S.freed x a = S'.freed x a := by
  unfold Memories.freed
  rcases List.IsRefinedBy.getElem? (h.2.1 x) a with ⟨h₁, h₂⟩ | ⟨b, b', h₁, h₂, hb⟩
  · rw [h₁, h₂]
  · rw [h₁, h₂]
    exact congrArg (!·) hb.2.2.1

variable {μ : Nat → Mem} {s s' : TraceState Mem unit}

/-- Traced states that refine each other show each pointer alike. -/
theorem TraceState.worldPtr_eq (h : s ⊑ s') : s.worldPtr μ = s'.worldPtr μ := by
  funext n p
  unfold TraceState.worldPtr TraceState.handles Renaming.ptr
  rw [h.2]
  split
  · rfl
  · rw [Memory.Memories.freed_eq h.1]

/-- A value and one that refines it, seen from traced states that refine
each other, are seen as a value and one that refines it. -/
theorem TraceState.worldVal_isRefinedBy {V : Type} [HRefinement V V] [HasPtrs V] (h : s ⊑ s')
    {v v' : V} (hv : v ⊑ v') : s.worldVal μ v ⊑ s'.worldVal μ v' := by
  unfold TraceState.worldVal
  rw [← TraceState.worldPtr_eq h]
  exact HasPtrs.map_mono _ hv

/-- A unit and one that refines it, seen from traced states that refine
each other, are seen as a unit and one that refines it. -/
theorem TraceState.worldUnit_isRefinedBy (h : s ⊑ s') {u : Nat} :
    ∀ {v v' : MemUnit u}, v ⊑ v' → s.worldUnit μ v ⊑ s'.worldUnit μ v'
  | .poison, _, _ => trivial
  | .bits _, _, hv => by
    cases (hv : _ = _)
    exact WUnit.isRefinedBy_refl _
  | .frag .., _, hv => by
    cases (hv : _ = _)
    unfold TraceState.worldUnit
    rw [← TraceState.worldPtr_eq h]
    exact WUnit.isRefinedBy_refl _

/-- Units that refine others one by one, seen from traced states that refine
each other, are seen as units that refine the others one by one. -/
theorem TraceState.worldUnits_isRefinedBy (h : s ⊑ s') {u : Nat} :
    ∀ {l l' : List (MemUnit u)}, l ⊑ l' → l.map (s.worldUnit μ) ⊑ l'.map (s'.worldUnit μ)
  | [], [], _ => trivial
  | _ :: _, _ :: _, hl => ⟨TraceState.worldUnit_isRefinedBy h hl.1,
    TraceState.worldUnits_isRefinedBy h hl.2⟩
  | [], _ :: _, hl | _ :: _, [], hl => (hl : False).elim

/-- Traced states that refine each other let the world see units that refine
each other, allocation by allocation. -/
theorem TraceState.seen_isRefinedBy (h : s ⊑ s') : s.seen μ ⊑ s'.seen μ := by
  unfold TraceState.seen
  rw [← h.2]
  induction s.escaped with
  | nil => exact trivial
  | cons p l ih =>
    refine ⟨?_, ih⟩
    obtain ⟨x, a⟩ := p
    rcases List.IsRefinedBy.getElem? (h.1.2.1 x) a with ⟨h₁, h₂⟩ | ⟨b, b', h₁, h₂, hb⟩
    · simp only [h₁, h₂]
      exact trivial
    · simp only [h₁, h₂, ← hb.2.2.1]
      split
      · exact TraceState.worldUnits_isRefinedBy h (hb.2.2.2.2.2.2 ‹_›)
      · exact trivial

end Fir
