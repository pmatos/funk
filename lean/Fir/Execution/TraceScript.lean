import Fir.Execution.Trace

/-!
# Scripted worlds

A test gives the world as a _script_: the answer to each event, in the order
the run shows them (ADR-2026-11-09-1540). The answer to an event that hands
control to code outside the program, shown by `TraceM.ask`, holds the
world's actions on escaped memory too: its writes into escaped allocations,
and the heap allocations it creates and frees
(`Fir.Execution.TraceWorld`). `fir-ref run` takes a script, and the harness
generates from the same script the stubs that answer a native run
(`docs/decisions/semantics-m1-trace.md#scripts-and-native-runs`).

A script is a world: it answers the event shown after `k` acts with its
answer at place `k`, and with a default answer past its end. A finite
outcome _follows_ the script when the answers of its trace are the script,
in order: it is shown at the script's world, and it shows as many acts as
the script has answers. So a script that answers fewer events than a run
shows, or more, fits none of its outcomes, as a choice sequence that is too
short or too long fits no path of a run.
-/

namespace Fir

variable {E Ans O : Type}

/-- A scripted world: the answer to each event, in order. -/
abbrev WorldScript (Ans : Type) : Type := List Ans

/-- The world that a script gives: the answer at place `k` of the script to
the event shown after `k` acts, and the default answer past its end. -/
def WorldScript.world [Inhabited Ans] (sc : WorldScript Ans) : World E Ans :=
  fun before _ => sc.getD before.length default

/-- A finite outcome follows the script `sc` when the answers of its trace
are the script, in order. An outcome that shows acts forever follows no
script. -/
def TOutcome.Follows (sc : WorldScript Ans) : TOutcome (Act E Ans) O → Prop
  | .ret tr _ | .ub tr _ | .diverge tr => tr.map (·.answer) = sc
  | .reacts _ => False

/-- The trace of a finite outcome: its acts in order. -/
def TOutcome.trace? {A : Type} : TOutcome A O → Option (List A)
  | .ret tr _ | .ub tr _ | .diverge tr => some tr
  | .reacts _ => none

/-- A finite outcome follows a script exactly when it is shown at the
script's world and shows as many acts as the script has answers. -/
theorem TOutcome.follows_iff [Inhabited Ans] (sc : WorldScript Ans) (t : TOutcome (Act E Ans) O)
    (tr : List (Act E Ans)) (ht : t.trace? = some tr) :
    t.Follows sc ↔ t.InWorld sc.world ∧ tr.length = sc.length := by
  have hact : ∀ i, t.act? i = tr[i]? := by
    intro i; cases t <;> simp_all [trace?, act?]
  have hfol : t.Follows sc ↔ tr.map (·.answer) = sc := by
    cases t <;> simp_all [trace?, Follows]
  have hbefore : ∀ i a, t.act? i = some a → (t.before i).length = i := fun _ _ h => before_length h
  rw [hfol]
  constructor
  · rintro rfl
    refine ⟨fun i a ha => ?_, by simp⟩
    rw [hact] at ha
    show a.answer = (tr.map (·.answer)).getD (t.before i).length default
    rw [hbefore i a (by rw [hact]; exact ha), List.getD_eq_getElem?_getD, List.getElem?_map, ha]
    rfl
  · rintro ⟨hw, hl⟩
    apply List.ext_getElem (by simpa using hl)
    intro i h₁ h₂
    have hi : i < tr.length := by simpa using h₁
    have ha : t.act? i = some tr[i] := by rw [hact]; exact List.getElem?_eq_getElem hi
    have := hw i _ ha
    rw [List.getElem_map, this]
    show sc.getD (t.before i).length default = _
    rw [hbefore i _ ha, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]
    simp

end Fir
