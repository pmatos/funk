import Fir.Memory.Refine
import Fir.Execution.MemoryTotal

/-!
# Monotonicity with memory

Refinement through a run asks each op that runs by its own rule to be
monotone (the section on poison obligations): on operands that refine
others, each way it may end is allowed by a way it may end on those others.
An op that touches memory has no semantics in the set monad, so this
obligation speaks of the op's semantics with memory, as the effect
obligations and totality do
(`docs/decisions/semantics-interpreter.md#memory-and-progress-with-memory`;
`docs/decisions/semantics-effects.md#soundness`).
Its operands may refine others, and so may the memories it starts from
(the section on refining memories):

* _Monotone with memory_: wherever a run names the dialect's memories, on
  operands that refine others and from memories that refine others, each
  way an op that is not a terminator may end is allowed by a way it may end
  on those others: UB, which allows anything, or results that the first's
  refine, with memories that the first's refine. A terminator goes to the
  same place, with memories that refine the others'.

It looks only at what runs by the op's own rule, and speaks only of valid
op instances, as monotonicity in the set monad does.

A computation of the set monad, run in the state layer, keeps the memories
it starts from, so it keeps their refinement. So an op that is tied, as
every op that touches no memory is, is monotone with memory when it is
monotone in the set monad. In a dialect that lifts the set monad, every op
is tied, an op is monotone with memory exactly when it is monotone in the
set monad, and a lawful dialect is lawful in its monotonicity. A sum and a
lift run an op of a side by that side's rule with its results mapped (the
section on the monotonicity of a sum and a lift).

A dialect meets the obligation by being _lawful in its monotonicity_, the
class below. The class asks for no semantics in the set monad, so a dialect
whose ops touch memory can meet it.
-/

namespace Fir

open Memory

variable {σ α β : Type} [HRefinement σ σ]

/-! # Computations that refine others, with memory -/

/-- The computation `c'` of the state layer refines `c`, by `r` on what they
give: from states that refine others, each way `c'` may end is allowed by a
way `c` may end from those others, UB or a result related by `r` with a
state that the other's refines. -/
def StateRefinedBy (r : α → α → Prop) (c c' : StateT σ SetM α) : Prop :=
  ∀ S S', S ⊑ S' → SetM.IsRefinedBy (fun p p' => r p.1 p'.1 ∧ p.2 ⊑ p'.2) (c S) (c' S')

/-- Computations of the set monad, run in the state layer, refine each
other as they do in the set monad: they keep the states. -/
theorem StateRefinedBy.lift {r : α → α → Prop} {s t : SetM α} (h : SetM.IsRefinedBy r s t) :
    StateRefinedBy r (StateT.lift s : StateT σ SetM α) (StateT.lift t) := by
  intro S S' hS e he
  rcases (SetM.lift_apply t S' e).1 he with ⟨a', ha', rfl⟩ | ⟨r', hr', rfl⟩
  · obtain ⟨e₀, he₀, hle⟩ := h _ ha'
    cases e₀ with
    | ok a => exact ⟨.ok (a, S), (SetM.lift_apply s S _).2 (.inl ⟨a, he₀, rfl⟩), hle, hS⟩
    | ub r₀ => exact ⟨.ub r₀, (SetM.lift_apply s S _).2 (.inr ⟨r₀, he₀, rfl⟩), trivial⟩
  · obtain ⟨e₀, he₀, hle⟩ := h _ hr'
    cases e₀ with
    | ok _ => exact absurd hle id
    | ub r₀ => exact ⟨.ub r₀, (SetM.lift_apply s S _).2 (.inr ⟨r₀, he₀, rfl⟩), trivial⟩

/-- Computations of the set monad that, run in the state layer, refine each
other from one state refine each other in the set monad. -/
theorem StateRefinedBy.of_lift {r : α → α → Prop} {s t : SetM α}
    (h : StateRefinedBy r (StateT.lift s : StateT σ SetM α) (StateT.lift t)) {S : σ} (hS : S ⊑ S) :
    SetM.IsRefinedBy r s t := by
  intro e he
  cases e with
  | ok a' =>
    obtain ⟨e₀, he₀, hle⟩ := h S S hS (.ok (a', S)) ((SetM.lift_apply t S _).2 (.inl ⟨a', he, rfl⟩))
    rcases (SetM.lift_apply s S e₀).1 he₀ with ⟨a, ha, rfl⟩ | ⟨r₀, hr₀, rfl⟩
    · exact ⟨.ok a, ha, hle.1⟩
    · exact ⟨.ub r₀, hr₀, trivial⟩
  | ub r' =>
    obtain ⟨e₀, he₀, hle⟩ := h S S hS (.ub r') ((SetM.lift_apply t S _).2 (.inr ⟨r', he, rfl⟩))
    rcases (SetM.lift_apply s S e₀).1 he₀ with ⟨a, _, rfl⟩ | ⟨r₀, hr₀, rfl⟩
    · exact absurd hle id
    · exact ⟨.ub r₀, hr₀, trivial⟩

/-- Mapping the results of two computations by a map that keeps the
relation keeps refinement. -/
theorem StateRefinedBy.map {r : α → α → Prop} {r' : β → β → Prop} (f : α → β)
    (hf : ∀ {a a'}, r a a' → r' (f a) (f a')) {c c' : StateT σ SetM α}
    (h : StateRefinedBy r c c') : StateRefinedBy r' (f <$> c) (f <$> c') := by
  intro S S' hS e he
  rcases (SetM.stateMap_apply f c' S' e).1 he with ⟨a', T', ha', rfl⟩ | ⟨r₁, hr₁, rfl⟩
  · obtain ⟨e₀, he₀, hle⟩ := h S S' hS _ ha'
    cases e₀ with
    | ok p => exact ⟨.ok (f p.1, p.2), (SetM.stateMap_apply f c S _).2 (.inl ⟨p.1, p.2, he₀, rfl⟩),
        hf hle.1, hle.2⟩
    | ub r₀ => exact ⟨.ub r₀, (SetM.stateMap_apply f c S _).2 (.inr ⟨r₀, he₀, rfl⟩), trivial⟩
  · obtain ⟨e₀, he₀, hle⟩ := h S S' hS _ hr₁
    cases e₀ with
    | ok _ => exact absurd hle id
    | ub r₀ => exact ⟨.ub r₀, (SetM.stateMap_apply f c S _).2 (.inr ⟨r₀, he₀, rfl⟩), trivial⟩

/-! # The obligation -/

section

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [TyRefinement d.Ty]

/-- In a semantics in the state layer, the op is monotone: on operands that
refine others, what it runs by its own rule refines what it runs on those
others, from memories that refine others. -/
def OpMemMonotone [DialectDenote d (StateT σ SetM)] (op : d.Op) : Prop :=
  ∀ args args' : HVector toType (sig op), args.Forall₂ TyRefinement.IsRefinedBy args' →
    (isTerminator op = false → StateRefinedBy (HVector.Forall₂ TyRefinement.IsRefinedBy)
        (DialectDenote.denote (m := StateT σ SetM) op args)
        (DialectDenote.denote (m := StateT σ SetM) op args')) ∧
      (isTerminator op = true → StateRefinedBy Eq (DialectDenote.exit (m := StateT σ SetM) op args)
        (DialectDenote.exit (m := StateT σ SetM) op args'))

variable [DialectEffects d] [DialectMemDenote d]

/-- Monotone with memory: wherever a run names the dialect's memories, the
op is monotone in its semantics with memory at that naming. -/
def MemMonotone (op : d.Op) : Prop :=
  ∀ {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N),
    letI := DialectMemDenote.denoteAt (d := d) lay ρ
    OpMemMonotone (σ := Memories N (unitsOf lay)) op

/-- A dialect lawful in its monotonicity: every valid instance that runs by
its own rule, a terminator or an op with no callee, is monotone with
memory. -/
class LawfulDialectMonotone (d : Dialect) [TyDenote d.Ty] [DialectSignature d] [TyRefinement d.Ty]
    [DialectEffects d] [DialectCall d] [DialectValidation d] [DialectMemDenote d] : Prop where
  monotone : ∀ op : d.Op, TypesValid op → isTerminator op = true ∨ callee? op = none →
    MemMonotone op

end

/-! # Ops that touch no memory -/

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [TyRefinement d.Ty] [DialectEffects d]
  [DialectDenote d SetM] [DialectMemDenote d]

/-- An op that touches no memory and is monotone in the set monad is
monotone with memory. -/
theorem MemMonotone.ofLifts {op : d.Op} (hl : OpLiftsSetM op) (h : OpMonotone op) :
    MemMonotone op :=
  fun lay ρ args args' hr => by
    rw [(hl lay ρ args).1, (hl lay ρ args).2, (hl lay ρ args').1, (hl lay ρ args').2]
    exact ⟨fun ht => StateRefinedBy.lift ((h args args' hr).1 ht),
      fun ht => StateRefinedBy.lift ((h args args' hr).2 ht)⟩

variable [LiftsSetM d]

/-- In a dialect that lifts the set monad, an op monotone with memory is
monotone in the set monad. -/
theorem MemMonotone.setM {op : d.Op} (h : MemMonotone op) : OpMonotone op := by
  intro args args' hr
  have hu := h (N := Unit) (fun _ => MemLayout.default) (fun _ => ())
  unfold OpMemMonotone at hu
  rw [LiftsSetM.lifts] at hu
  have hS := Memories.isRefinedBy_refl
    (Memories.empty : Memories Unit (unitsOf fun _ => MemLayout.default))
  exact ⟨fun ht => ((hu args args' hr).1 ht).of_lift hS,
    fun ht => ((hu args args' hr).2 ht).of_lift hS⟩

/-- A lawful dialect that lifts the set monad is lawful in its
monotonicity: its monotonicity in the set monad holds with memory. -/
theorem LawfulDialectMonotone.ofLawful [DialectCall d] [DialectValidation d] [TyPoison d.Ty]
    [LawfulDialectPoison d] : LawfulDialectMonotone d where
  monotone op hv hc :=
    MemMonotone.ofLifts (LiftsSetM.opLifts op) (LawfulDialectPoison.monotone op hv hc)

end Fir
