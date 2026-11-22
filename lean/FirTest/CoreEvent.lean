import Fir

/-!
Tests of the core's events (#239, stage 3a): what the world sees of values
and of escaped memory, how one event refines another, and that the sum of
the core and `gpu` shows the core's events.
-/

namespace FirTest.CoreEvent

open Fir Fir.Memory Fir.Core

/-- Memories whose units are bytes. -/
abbrev w : Nat → Nat := fun _ => 8

/-- A traced state whose memory 0 holds three allocations: the first, which
holds the byte 5 and a fragment of a pointer into the second, escaped with
the handle 0; the second, live, which has not escaped; and the third,
freed, which escaped with the handle 1. -/
def s : TraceState Nat w :=
  ⟨Memories.empty.set 0 ⟨[⟨.global, 1, [.bits 5, .frag 0 ⟨some 1, 0⟩ 0], true, none, false⟩,
    ⟨.global, 1, [.bits 6], true, none, false⟩,
    ⟨.heap, 1, [.bits 7], false, none, false⟩]⟩, [(0, 0), (0, 2)]⟩

/-! # What the world sees -/

-- A pointer with no provenance is itself; one into the escaped allocation
-- names it by its handle; one into the allocation that has not escaped, or
-- into the freed one, is poison.
#guard s.worldPtr id 0 ⟨none, 3⟩ == some ⟨none, 3⟩
#guard s.worldPtr id 0 ⟨some 0, 1⟩ == some ⟨some 0, 1⟩
#guard s.worldPtr id 0 ⟨some 1, 0⟩ == none
#guard s.worldPtr id 0 ⟨some 2, 0⟩ == none

-- The world sees the units of the escaped live allocation, the fragment of a
-- pointer it cannot name as poison, and none of the freed allocation.
#guard s.seen id == [[.bits 5, .poison], []]

/-- A pointer argument into the escaped allocation is seen with its handle. -/
example : s.worldVal id ([⟨.ptr 0, .value ⟨some 0, 1⟩⟩] : List (DVal CoreDialect)) =
    [⟨.ptr 0, .value ⟨some 0, 1⟩⟩] := rfl

/-- A pointer argument into the allocation that has not escaped is seen as
poison. -/
example : s.worldVal id ([⟨.ptr 0, .value ⟨some 1, 0⟩⟩] : List (DVal CoreDialect)) =
    [⟨.ptr 0, .poison⟩] := rfl

/-! # Refinement of events -/

/-- An external call on a poison argument is refined by the same call on a
value, and a poison unit the world sees by a unit of bits. -/
example : Event.call "g" [⟨.int 8, .poison⟩] [[.poison]] ⊑
    Event.call "g" [⟨.int 8, .value 5⟩] [[.bits 5]] :=
  ⟨rfl, ⟨⟨rfl, trivial⟩, trivial⟩, ⟨⟨trivial, trivial⟩, trivial⟩⟩

/-- A call of one symbol is not refined by a call of another. -/
example : ¬ Event.call "g" [] [] ⊑ Event.call "h" [] [] := fun h => nomatch h.1

/-- A call on a value is not refined by the same call on another value. -/
example : ¬ Event.call "g" [⟨.int 8, .value 5⟩] [] ⊑ Event.call "g" [⟨.int 8, .value 6⟩] [] :=
  fun ⟨_, ⟨⟨_, h⟩, _⟩, _⟩ => nomatch h

/-- The event of an external call from `s` on a pointer into the escaped
allocation. -/
example : Event.ofCall id s "g" [⟨.ptr 0, .value ⟨some 0, 1⟩⟩] =
    .call "g" [⟨.ptr 0, .value ⟨some 0, 1⟩⟩] [[.bits 5, .poison], []] := by
  simp only [Event.ofCall]
  exact congrArg _ (by decide)

/-! # The sum of the core and `gpu` -/

section

variable [Gpu.WorkItem]

/-- The sum shows the core's events, since `gpu` shows none. -/
example : DialectTrace.Event CoreGpu = (Core.Event ⊕ Empty) := rfl

/-- And the world answers them as it answers the core's. -/
example : DialectTrace.Answer CoreGpu = ((Core.Reply × List WorldAct) ⊕ Unit) := rfl

end

/-! # Axioms -/

/-- info: 'Fir.TraceState.seen_isRefinedBy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.TraceState.seen_isRefinedBy

/-- info: 'Fir.Core.Event.ofCall_isRefinedBy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.Event.ofCall_isRefinedBy

/-- info: 'Fir.Dialect.sum.liftsMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Dialect.sum.liftsMem

end FirTest.CoreEvent
