import Fir.Core.Observe
import Fir.Execution.TraceSeen

/-!
# The core's events

A run of the core shows an ordered trace of events (ADR-2026-11-09-1540).
The core has one kind of event so far, an _external call_: a call of a
function that funk did not compile, an external declaration. The volatile
accesses of #238 and the observable inline assembly of #240 add their own
kinds, each a constructor of the event type.

An external call shows, as the world sees them (`Fir.Execution.TraceSeen`):

* the symbol of the declaration it calls;
* its arguments, each pointer naming its allocation by its handle, and a
  pointer into an allocation that the world cannot name, such as a
  dangling one, as poison;
* the units of every escaped allocation, by handle, after the call has let
  escape each allocation that its pointer arguments, or the allocations
  that already escaped, reach, since outside code can read memory that
  escaped earlier. The human ruled this on 2026-11-20, on #239.

The world answers it with the call's results, each pointer naming its
allocation by its handle, and with its actions on escaped memory, which
`TraceM.ask` takes.

One event refines another when both call the same symbol, and the other's
arguments and units refine its own one by one, poison by any value: the
world answers what the target shows (the human's ruling of 2026-11-18 on
#233). Traced states that refine each other show, for arguments that refine
others, events that refine each other.

The run hands a call to a declaration to the core's external-call rule,
which shows this event (the human's ruling of 2026-11-21 on #239, Q1). That
rule is defined (`Fir.Core.ExtCallRule`) but not yet installed: until
#239's next stage makes it the core's, no run of the core shows an
event.
-/

namespace Fir.Core

open Memory

/-- An event of the core: `call g args seen`, an external call of the
declaration `g` on the arguments `args`, as the world sees them, when the
world sees the units `seen` of the escaped allocations, by handle. -/
inductive Event where
  | call (callee : Name) (args : List (DVal CoreDialect)) (seen : List (List WUnit))

/-- The world's answer to an external call: its results, each pointer naming
its allocation by its handle. Its actions on escaped memory come with it,
by `TraceM.ask`. -/
abbrev Reply : Type := List (DVal CoreDialect)

/-- An event is refined by an event of the same symbol whose arguments and
units refine its own one by one, poison by any value. -/
def Event.IsRefinedBy : Event → Event → Prop
  | .call g args seen, .call g' args' seen' => g = g' ∧ args ⊑ args' ∧ seen ⊑ seen'

instance : HRefinement Event Event := ⟨Event.IsRefinedBy⟩

/-- Refinement of events is reflexive. -/
theorem Event.isRefinedBy_refl : ∀ ev : Event, ev ⊑ ev
  | .call .. => ⟨rfl, List.isRefinedBy_refl
    (fun (v : DVal CoreDialect) => (⟨rfl, Ty.isRefinedBy_refl v.2⟩ : v ⊑ v)) _,
    List.isRefinedBy_refl (List.isRefinedBy_refl WUnit.isRefinedBy_refl) _⟩

/-- Refinement of events is transitive. -/
theorem Event.isRefinedBy_trans : ∀ {e₁ e₂ e₃ : Event}, e₁ ⊑ e₂ → e₂ ⊑ e₃ → e₁ ⊑ e₃
  | .call .., .call .., .call .., ⟨rfl, ha, hs⟩, ⟨rfl, ha', hs'⟩ =>
    ⟨rfl, List.isRefinedBy_trans (DVal.isRefinedBy_trans (d := CoreDialect) Ty.isRefinedBy_trans) ha ha',
      List.isRefinedBy_trans (List.isRefinedBy_trans WUnit.isRefinedBy_trans) hs hs'⟩

variable {N : Type} [DecidableEq N] {w : N → Nat} (μ : Nat → N)

/-- The event that an external call of the declaration `g` on the arguments
`args` shows from the traced state `s`, once it has let escape what it
reaches: the symbol, the arguments and the units of the escaped
allocations, as the world sees them. -/
def Event.ofCall (s : TraceState N w) (g : Name) (args : List (DVal CoreDialect)) : Event :=
  .call g (s.worldVal μ args) (s.seen μ)

/-- From traced states that refine each other, an external call on arguments
that refine others shows an event that refines the other's. -/
theorem Event.ofCall_isRefinedBy {s s' : TraceState N w} (h : s ⊑ s') (g : Name)
    {args args' : List (DVal CoreDialect)} (ha : args ⊑ args') :
    Event.ofCall μ s g args ⊑ Event.ofCall μ s' g args' :=
  ⟨rfl, TraceState.worldVal_isRefinedBy h ha, TraceState.seen_isRefinedBy h⟩

end Fir.Core
