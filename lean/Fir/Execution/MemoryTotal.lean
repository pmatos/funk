import Fir.Execution.MemoryObligationLaws

/-!
# Totality with memory

Progress asks each op that runs by its own rule, a terminator or an op with
no callee, to have a way to go on (the section on progress with calls). An
op that touches memory has no semantics in the set monad, so this
obligation speaks of the op's semantics with memory, as the effect
obligations do (`docs/decisions/semantics-interpreter.md#memory-and-progress-with-memory`;
`docs/decisions/semantics-effects.md#soundness`):

* _Total with memory_: wherever a run names the dialect's memories, from
  any memories, on every operand vector, an op that is not a terminator has
  an outcome, and so does the exit of a terminator. The outcome is a result
  with the memories after it, or UB.

It looks only at what runs by the op's own rule, and speaks only of valid
op instances, as the poison obligations do. An op with a callee goes on by
its callee's run, and needs no rule of its own (ADR-2026-10-29-2006).

It holds as the obligation on may-UB does:

* a computation of the set monad that has an outcome, run in the state
  layer, has one from any memories, and keeps them;
* mapping the results of a computation keeps an outcome.

So an op that is tied, as every op that touches no memory is, is total
with memory when it is total in the set monad. In a dialect that lifts the
set monad, every op is tied, an op is total with memory exactly when it is
total in the set monad, and a lawful dialect is lawful in its totality. A sum and a
lift run an op of a side by that side's rule with its results mapped, so
they are lawful in their totality when their sides are (the section on the
totality of a sum and a lift).

A dialect meets the obligation by being _lawful in its totality_, the
class below. The class asks for no semantics in the set monad, so a dialect
whose ops touch memory can meet it.
-/

namespace Fir

open Memory

variable {σ α β : Type}

/-! # Computations with an outcome -/

/-- The computation `c` of the state layer has an outcome from any state: a
result with the state after it, or UB. -/
def HasOutcome (c : StateT σ SetM α) : Prop :=
  ∀ S, ∃ e, c S e

/-- Mapping the results keeps an outcome. -/
theorem HasOutcome.map (f : α → β) {c : StateT σ SetM α} (h : HasOutcome c) :
    HasOutcome (f <$> c) := by
  intro S
  obtain ⟨e, he⟩ := h S
  cases e with
  | ok p => exact ⟨.ok (f p.1, p.2), (SetM.stateMap_apply f c S _).2 (.inl ⟨p.1, p.2, he, rfl⟩)⟩
  | ub r => exact ⟨.ub r, (SetM.stateMap_apply f c S _).2 (.inr ⟨r, he, rfl⟩)⟩

/-- A computation of the set monad that has an outcome, run in the state
layer, has one from any state. -/
theorem hasOutcome_lift {c : SetM α} (h : ∃ e, c e) :
    HasOutcome (StateT.lift c : StateT σ SetM α) := by
  intro S
  obtain ⟨e, he⟩ := h
  cases e with
  | ok a => exact ⟨.ok (a, S), (SetM.lift_apply c S _).2 (.inl ⟨a, he, rfl⟩)⟩
  | ub r => exact ⟨.ub r, (SetM.lift_apply c S _).2 (.inr ⟨r, he, rfl⟩)⟩

/-- A computation of the set monad that, run in the state layer, has an
outcome from some state has an outcome. -/
theorem HasOutcome.of_lift {c : SetM α} (h : HasOutcome (StateT.lift c : StateT σ SetM α))
    (S : σ) : ∃ e, c e := by
  obtain ⟨e, he⟩ := h S
  rcases (SetM.lift_apply c S e).1 he with ⟨_, ha, -⟩ | ⟨_, hr, -⟩
  · exact ⟨_, ha⟩
  · exact ⟨_, hr⟩

/-! # The obligation -/

/-- In a semantics in the state layer, what the op runs by its own rule has
an outcome from any state, on every operand vector: its meaning when it is
not a terminator, and its exit when it is. -/
def OpHasOutcome {d : Dialect} [TyDenote d.Ty] [DialectSignature d]
    [DialectDenote d (StateT σ SetM)] (op : d.Op) : Prop :=
  ∀ args : HVector toType (sig op),
    (isTerminator op = false →
      HasOutcome (DialectDenote.denote (m := StateT σ SetM) op args)) ∧
    (isTerminator op = true → HasOutcome (DialectDenote.exit (m := StateT σ SetM) op args))

section

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectEffects d]
  [DialectMemDenote d]

/-- Total with memory: wherever a run names the dialect's memories, on
every operand vector, an op that is not a terminator has an outcome from
any memories, and so does the exit of a terminator. -/
def MemTotal (op : d.Op) : Prop :=
  ∀ {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N),
    OwnRuleHas lay ρ HasOutcome op

/-- A dialect lawful in its totality: every valid instance that runs by its
own rule, a terminator or an op with no callee, is total with memory. -/
class LawfulDialectTotal (d : Dialect) [TyDenote d.Ty] [DialectSignature d] [DialectEffects d]
    [DialectCall d] [DialectValidation d] [DialectMemDenote d] : Prop where
  total : ∀ op : d.Op, TypesValid op → isTerminator op = true ∨ callee? op = none → MemTotal op

end

/-! # Ops that touch no memory -/

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectEffects d]
  [DialectDenote d SetM] [DialectMemDenote d]

/-- An op that touches no memory and is total in the set monad is total
with memory. -/
theorem MemTotal.ofLifts {op : d.Op} (hl : OpLiftsSetM op) (h : OpTotal op) : MemTotal op :=
  fun lay ρ args => by
    rw [(hl lay ρ args).1, (hl lay ρ args).2]
    exact ⟨fun ht => hasOutcome_lift ((h args).1 ht), fun ht => hasOutcome_lift ((h args).2 ht)⟩

variable [LiftsSetM d]

/-- In a dialect that lifts the set monad, an op total with memory is total
in the set monad. -/
theorem MemTotal.setM {op : d.Op} (h : MemTotal op) : OpTotal op := by
  intro args
  have hu := h (N := Unit) (fun _ => MemLayout.default) (fun _ => ()) args
  rw [LiftsSetM.lifts] at hu
  exact ⟨fun ht => (hu.1 ht).of_lift Memories.empty, fun ht => (hu.2 ht).of_lift Memories.empty⟩

/-- A lawful dialect that lifts the set monad is lawful in its totality: its
totality in the set monad holds with memory. -/
theorem LawfulDialectTotal.ofLawful [DialectCall d] [DialectValidation d] [TyPoison d.Ty]
    [TyRefinement d.Ty] [LawfulDialectPoison d] : LawfulDialectTotal d where
  total op hv hc := MemTotal.ofLifts (LiftsSetM.opLifts op) (LawfulDialectPoison.total op hv hc)

end Fir
