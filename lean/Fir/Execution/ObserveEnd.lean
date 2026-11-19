import Fir.Execution.Observe

/-!
# The end of a return

At a return an observer sees (ADR-2026-11-09-1540):

* the returned values;
* the allocations that escaped to the world, in the order they escaped;
* the live memory reachable from the returned pointers and from what
  escaped. The `export` globals join these roots when the module has them
  (#237).

Two ends of a run are compared up to a one-to-one renaming of allocations.
The end `s` of the source is refined by the end `t` of the target when some
one-to-one renaming `R` _shows_ `s` in `t`:

* `R` renames the allocation at each place of `s`'s list of escaped
  allocations to the one at the same place of `t`'s, which is as long. The
  world names an escaped allocation by its place in that list, so this
  renaming is fixed;
* `R` renames each allocation that a returned pointer of the source points
  into, unless the pointer is dangling, and `s`'s returned values, with
  each pointer renamed and each dangling one poison, are refined by `t`'s;
* each allocation that `R` renames is seen in its image: both are blocks of
  the same kind, alignment, liveness and size, whose addresses the address
  rule relates, or neither is an allocation that the run made. While the
  source's block is live, `R` renames each allocation that its units point
  into, unless the pointer is dangling, and its units, renamed so, are
  refined by the target's. So `R` renames every allocation that the
  observer reaches (`End.SeenUnder.reachable`), and the memory that no
  observer reaches is never compared: a store to it may be removed.

A freed allocation that the observer reaches is seen in a freed one, and
its contents are not compared: only live allocations are.

Whether the end of a run compares the addresses of exposed allocations is
open for the human (#233): this section takes the rule as a parameter, an
`AddrRule`, and every law holds for each rule that is reflexive and
transitive.

Refinement of the ends of runs is reflexive and transitive. When the source
returns no pointer and nothing escaped, it is the refinement of the
returned values: M0's runs, which return no pointer and show no event, keep
their refinement.
-/

namespace Fir

open Memory

/-- How the end of a run compares the addresses of two allocations that the
renaming relates (#232): a reflexive and transitive relation on their
addresses, each `none` until the allocation is exposed. -/
structure AddrRule where
  /-- The source's address is matched by the target's. -/
  rel : Option Nat → Option Nat → Prop
  refl : ∀ a, rel a a
  trans : ∀ {a b c}, rel a b → rel b c → rel a c

/-- The candidate rules, of which the human picks one (#233). `ignore`: the
end of a run does not compare addresses, as raw addresses are never compared
(ADR-2026-11-09-1540), and only the integers a run shows carry them. -/
def AddrRule.ignore : AddrRule := ⟨fun _ _ => True, fun _ => trivial, fun _ _ => trivial⟩

/-- `same`: two allocations that the renaming relates have the same address,
or neither has one, as refinement of blocks compares them (#232). -/
def AddrRule.same : AddrRule := ⟨Eq, fun _ => rfl, Eq.trans⟩

/-- `exposed`: two allocations that the renaming relates are both exposed or
neither is, whatever their addresses. -/
def AddrRule.exposed : AddrRule :=
  ⟨fun a b => a.isSome = b.isSome, fun _ => rfl, Eq.trans⟩

variable {u : Nat}

/-- A block of the source is seen in a block of the target, its pointers
replaced by `f`: both have the same kind, alignment, liveness and size,
their addresses are related by `ar`, and while it is live, its units,
replaced so, are refined by the target's. -/
def Memory.Block.SeenIn (ar : AddrRule) (f : Nat → Pointer → Option Pointer) (b b' : Block u) :
    Prop :=
  b.kind = b'.kind ∧ b.align = b'.align ∧ b.live = b'.live ∧
    b.units.length = b'.units.length ∧ ar.rel b.addr b'.addr ∧
    (b.live → HasPtrs.map f b.units ⊑ b'.units)

/-- An allocation of the source is seen in one of the target: both are
blocks, the first seen in the second, or neither is. -/
def Memory.Block.OptSeenIn (ar : AddrRule) (f : Nat → Pointer → Option Pointer) :
    Option (Block u) → Option (Block u) → Prop
  | none, none => True
  | some b, some b' => b.SeenIn ar f b'
  | _, _ => False

/-- The end of a return: the returned values, the memories, and the
allocations that escaped to the world, each by its memory, in the order
they escaped. Its refinement names each memory number `n` as `μ n`, and
compares addresses by `ar`. -/
structure End {Mem : Type} (unit : Mem → Nat) (μ : Nat → Mem) (ar : AddrRule) (V : Type) where
  vals : V
  mem : Memories Mem unit
  escaped : List (Mem × AllocId)

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem] {μ : Nat → Mem} {ar : AddrRule}
  {V : Type} [HRefinement V V] [HasPtrs V]

namespace End

/-- The renaming `R` shows the end `s` of the source in the end `t` of the
target. -/
def SeenUnder (R : Renaming Mem) (s t : End unit μ ar V) : Prop :=
  R.Injective ∧
  s.escaped.length = t.escaped.length ∧
  (∀ (i : Nat) (e : Mem × AllocId), s.escaped[i]? = some e →
    ∃ e' : Mem × AllocId, t.escaped[i]? = some e' ∧ e.1 = e'.1 ∧ R e.1 e.2 = some e'.2) ∧
  (∀ n p, (n, p) ∈ HasPtrs.ptrs s.vals → R.Covers μ s.mem n p) ∧
  HasPtrs.map (R.ptr μ s.mem) s.vals ⊑ t.vals ∧
  ∀ x a a', R x a = some a' →
    Block.OptSeenIn ar (R.ptr μ s.mem) ((s.mem.mem x).blocks[a]?) ((t.mem.mem x).blocks[a']?) ∧
    ∀ b, (s.mem.mem x).blocks[a]? = some b → b.live →
      ∀ n p, (n, p) ∈ HasPtrs.ptrs b.units → R.Covers μ s.mem n p

/-- The end of a return is refined by another when some one-to-one renaming
shows it in the other. -/
instance : HRefinement (End unit μ ar V) (End unit μ ar V) := ⟨fun s t => ∃ R, SeenUnder R s t⟩

/-- An allocation that an observer reaches from the end of a return: an
escaped one; one that a returned pointer points into, unless the pointer is
dangling; and one that a unit of a live allocation it reaches points into,
unless that pointer is dangling. -/
inductive Reachable (s : End unit μ ar V) : Mem → AllocId → Prop
  | escaped {x a} : (x, a) ∈ s.escaped → Reachable s x a
  | val {n p a} : (n, p) ∈ HasPtrs.ptrs s.vals → p.prov = some a → s.mem.freed (μ n) a = false →
      Reachable s (μ n) a
  | unit {x a b n p c} : Reachable s x a → (s.mem.mem x).blocks[a]? = some b → b.live →
      (n, p) ∈ HasPtrs.ptrs b.units → p.prov = some c → s.mem.freed (μ n) c = false →
      Reachable s (μ n) c

/-- A renaming that shows the end of a return in another renames every
allocation that the observer reaches. -/
theorem SeenUnder.reachable {R : Renaming Mem} {s t : End unit μ ar V} (h : SeenUnder R s t)
    {x : Mem} {a : AllocId} (hr : s.Reachable x a) : (R x a).isSome := by
  induction hr with
  | escaped he =>
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 he
    obtain ⟨_, _, _, he'⟩ := h.2.2.1 i _ hi
    simp [he']
  | val hp hpa hf => exact h.2.2.2.1 _ _ hp _ hpa hf
  | unit _ hb hl hp hpa hf ih =>
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.1 ih
    exact (h.2.2.2.2.2 _ _ _ ha').2 _ hb hl _ _ hp _ hpa hf

end End

end Fir
