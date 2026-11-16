import Fir.Execution.MemoryObligationLaws
import Fir.Execution.MemoryTotal
import Fir.Execution.MemoryFinite
import Fir.Execution.MemoryOpRefine

/-!
# Sequences in the state layer

An op whose rule runs one computation of the state layer after another,
such as a load and then a store of the units it gave, meets an obligation
when each part does. This section proves it for the obligations that hold
of each path on its own: having an outcome, having finitely many, writing
no unit of a memory, neither allocating nor freeing in a memory, and
refinement from refining memories.

Not reading a memory does not follow this way. The obligation compares a
run from the memories `S` with a run from `S` with the memory `x`
replaced, and after the first part the second run's memories agree with
the first's off `x`, but need not be the first's with `x` replaced. So a
rule that does not read `x` proves it by its own parts' laws, as the copy
of units does in the next section.
-/

namespace Fir

open Memory

variable {σ α β : Type}

/-- The ways a sequence may end: as its second part may, after its first
part ends with a result, or in UB, as its first part may. -/
theorem SetM.stateBind_apply (c : StateT σ SetM α) (f : α → StateT σ SetM β) (S : σ)
    (e : Ev (β × σ)) :
    (c >>= f) S e ↔ (∃ a S₁, c S (.ok (a, S₁)) ∧ f a S₁ e) ∨ (∃ r, c S (.ub r) ∧ e = .ub r) := by
  show (∃ p, c S (.ok p) ∧ f p.1 p.2 e) ∨ _ ↔ _
  constructor
  · rintro (⟨⟨a, S₁⟩, hc, hf⟩ | h)
    · exact .inl ⟨a, S₁, hc, hf⟩
    · exact .inr h
  · rintro (⟨a, S₁, hc, hf⟩ | h)
    · exact .inl ⟨(a, S₁), hc, hf⟩
    · exact .inr h

variable {c : StateT σ SetM α} {f : α → StateT σ SetM β}

/-- A sequence has an outcome when its parts have one. -/
theorem HasOutcome.bind (hc : HasOutcome c) (hf : ∀ a, HasOutcome (f a)) :
    HasOutcome (c >>= f) := by
  intro S
  obtain ⟨e, he⟩ := hc S
  cases e with
  | ok p =>
    obtain ⟨e', he'⟩ := hf p.1 p.2
    exact ⟨e', (SetM.stateBind_apply c f S e').2 (.inl ⟨p.1, p.2, he, he'⟩)⟩
  | ub r => exact ⟨.ub r, (SetM.stateBind_apply c f S _).2 (.inr ⟨r, he, rfl⟩)⟩

/-- A sequence has finitely many outcomes when its parts have. -/
theorem FinitelyMany.bind (hc : FinitelyMany c) (hf : ∀ a, FinitelyMany (f a)) :
    FinitelyMany (c >>= f) := by
  intro S
  obtain ⟨L, hL⟩ := hc S
  refine ⟨L.flatMap fun p => Classical.choose (hf p.1 p.2), fun q hq => ?_⟩
  rcases (SetM.stateBind_apply c f S _).1 hq with ⟨a, S₁, hc', hf'⟩ | ⟨_, _, he⟩
  · exact List.mem_flatMap.2 ⟨(a, S₁), hL _ hc', Classical.choose_spec (hf a S₁) q hf'⟩
  · cases he

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {c : StateT (Memories Mem unit) SetM α} {f : α → StateT (Memories Mem unit) SetM β} {x : Mem}

/-- A sequence writes no unit of `x` when its parts write none. -/
theorem WritesNot.bind (hc : WritesNot x c) (hf : ∀ a, WritesNot x (f a)) :
    WritesNot x (c >>= f) := by
  intro S b S' h
  rcases (SetM.stateBind_apply c f S _).1 h with ⟨a, S₁, hc', hf'⟩ | ⟨_, _, he⟩
  · exact (hc S a S₁ hc').trans (hf a S₁ b S' hf')
  · cases he

/-- A sequence neither allocates nor frees in `x` when its parts do
neither. -/
theorem AllocatesNot.bind (hc : AllocatesNot x c) (hf : ∀ a, AllocatesNot x (f a)) :
    AllocatesNot x (c >>= f) := by
  intro S b S' h
  rcases (SetM.stateBind_apply c f S _).1 h with ⟨a, S₁, hc', hf'⟩ | ⟨_, _, he⟩
  · obtain ⟨h₁, h₂⟩ := hc S a S₁ hc'
    obtain ⟨h₃, h₄⟩ := hf a S₁ b S' hf'
    exact ⟨h₃.trans h₁, h₄.trans h₂⟩
  · cases he

/-- A sequence refines another when its first part refines the other's,
and its second part, after results related by `r`, refines the other's. -/
theorem StateRefinedBy.bind {τ : Type} [HRefinement τ τ] {r : α → α → Prop}
    {r' : β → β → Prop} {c c' : StateT τ SetM α} {f f' : α → StateT τ SetM β}
    (hc : StateRefinedBy r c c') (hf : ∀ a a', r a a' → StateRefinedBy r' (f a) (f' a')) :
    StateRefinedBy r' (c >>= f) (c' >>= f') := by
  intro S S' hS e he
  rcases (SetM.stateBind_apply c' f' S' e).1 he with ⟨a', S₁', hc', hf'⟩ | ⟨r₁, hr₁, rfl⟩
  · obtain ⟨e₀, he₀, hle⟩ := hc S S' hS _ hc'
    cases e₀ with
    | ok p =>
      obtain ⟨e₁, he₁, hle₁⟩ := hf p.1 a' hle.1 p.2 S₁' hle.2 e hf'
      exact ⟨e₁, (SetM.stateBind_apply c f S e₁).2 (.inl ⟨p.1, p.2, he₀, he₁⟩), hle₁⟩
    | ub r₀ => exact ⟨.ub r₀, (SetM.stateBind_apply c f S _).2 (.inr ⟨r₀, he₀, rfl⟩), trivial⟩
  · obtain ⟨e₀, he₀, hle⟩ := hc S S' hS _ hr₁
    cases e₀ with
    | ok _ => exact absurd hle id
    | ub r₀ => exact ⟨.ub r₀, (SetM.stateBind_apply c f S _).2 (.inr ⟨r₀, he₀, rfl⟩), trivial⟩

end Fir
