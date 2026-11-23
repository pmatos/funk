import Fir

/-!
Tests of the core's traced external-call rule (#239, stage 3b-2a): what a
call lets escape and in which order, how the world's reply is read back,
and the examples of the human's rulings Q4 and Q6 on #239, under which the
rule is monotone only when both calls let escape the same allocations, in
the same order.
-/

namespace FirTest.CoreExtCallRule

open Fir Fir.Memory Fir.Core

/-- Memories whose units are bytes. -/
abbrev w : Nat → Nat := fun _ => 8

/-- A live stack block of byte units. -/
def blk (us : List (MemUnit 8)) : Memory.Block 8 := ⟨.stack, 1, us, true, none, false⟩

/-- A traced state whose memory 0 holds the given blocks, with the escaped
list `esc`. -/
def st (bs : List (Memory.Block 8)) (esc : List (Nat × AllocId)) : TraceState Nat w :=
  ⟨Memories.empty.set 0 ⟨bs⟩, esc⟩

/-- A pointer into the allocation `a` of memory 0, as a unit. -/
def frag (a : AllocId) : MemUnit 8 := .frag 0 ⟨some a, 0⟩ 0

/-! # What a call lets escape -/

/-- Three allocations: `0` points into `1`, `1` into `2`, and `2` holds a
byte; nothing escaped. -/
def chain : TraceState Nat w := st [blk [frag 1], blk [frag 2], blk [.bits 3]] []

-- A pointer argument into `0` lets escape `0`, then what it points into, in
-- turn.
#guard (chain.escapeCall id [(0, ⟨some 0, 0⟩)]).escaped == [(0, 0), (0, 1), (0, 2)]
-- A pointer into `1` lets escape `1` and `2`, not `0`.
#guard (chain.escapeCall id [(0, ⟨some 1, 0⟩)]).escaped == [(0, 1), (0, 2)]
-- A pointer without provenance, or none at all, lets nothing escape.
#guard (chain.escapeCall id [(0, ⟨none, 4⟩)]).escaped == []
#guard (chain.escapeCall id []).escaped == []

/-- Allocation `1` escaped earlier; `0` is freed and `1` points into it. -/
def earlier : TraceState Nat w :=
  st [{ blk [.bits 0] with live := false }, blk [frag 0, frag 2], blk [.bits 3]] [(0, 1)]

-- A call with no argument still lets escape what escaped memory reaches,
-- after what had escaped, which keeps its handle; a freed allocation does
-- not escape.
#guard (earlier.escapeCall id []).escaped == [(0, 1), (0, 2)]

/-! # Q4: poison handed to the world -/

/-- What escapes from a traced state with nothing escaped, on arguments that
hold no pointer: nothing. -/
theorem escapeCall_nil (s : TraceState Nat w) (hs : s.escaped = []) :
    (s.escapeCall id []).escaped = [] := by
  rw [TraceState.escapeCall, TraceState.reach]
  simp [TraceState.escapePtrs, hs]


/-- `@f` has allocated `%l`, allocation `0`, and stored 1 into it. -/
def q4 : TraceState Nat w := st [blk [.bits 1]] []

/-- On poison, `%q` is poison. -/
def q4src : List (DVal CoreDialect) := [⟨.ptr 0, .poison⟩]

/-- On 0, `%q` is `%l`. -/
def q4tgt : List (DVal CoreDialect) := [⟨.ptr 0, .value ⟨some 0, 0⟩⟩]

-- The source lets nothing escape; the target lets `%l` escape.
#guard (q4.escapeCall id (HasPtrs.ptrs q4src)).escaped == []
#guard (q4.escapeCall id (HasPtrs.ptrs q4tgt)).escaped == [(0, 0)]

/-- The world writes 7 into the allocation of handle 0. -/
def write7 : List WorldAct := [.store 0 0 [.bits 7]]

-- In the target, the world can write 7 into `%l`, which a load then reads.
#guard ((WorldAct.applyAll id write7 (q4.escapeCall id (HasPtrs.ptrs q4tgt))).map
    fun t => (t.mem.mem 0).blocks[0]?.map (·.units)) == some (some [.bits 7])
-- In the source it cannot: no allocation has the handle 0.
#guard (WorldAct.applyAll id write7 (q4.escapeCall id (HasPtrs.ptrs q4src))).isNone

-- The target's event shows `%l` by its handle and its units; the source's
-- shows poison and no escaped memory.
#guard (q4.escapeCall id (HasPtrs.ptrs q4tgt)).seen id == [[.bits 1]]
#guard (q4.escapeCall id (HasPtrs.ptrs q4src)).seen id == []

/-- So the source has no outcome with the world's answer that writes 7: the
rule is not monotone without the condition on what escapes. -/
example (r : Reply) (vs : List (DVal CoreDialect)) (t : TraceState Nat w)
    (h : traceExtCall id "g" q4src [] q4 (.ok (vs, [⟨Event.ofCall id
      (q4.escapeCall id (HasPtrs.ptrs q4src)) "g" q4src, (r, write7)⟩], t))) : False := by
  obtain ⟨_, ws, _, _, hws, -, he⟩ := (traceExtCall_iff id).1 h
  simp only [Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, Act.mk.injEq, and_true] at he
  have hp : HasPtrs.ptrs q4src = [] := rfl
  rw [← he.2.1.2.2, hp] at hws
  simp [WorldAct.applyAll, WorldAct.apply, write7, escapeCall_nil q4 rfl] at hws

/-! # Q6: the same allocations, in another order -/

/-- The escaped allocation `0` holds poison, then pointers into `1` and `2`. -/
def q6src : TraceState Nat w := st [blk [.poison, frag 1, frag 2], blk [.bits 1], blk [.bits 2]] [(0, 0)]

/-- The target's holds pointers into `2`, `1` and `2`. -/
def q6tgt : TraceState Nat w := st [blk [frag 2, frag 1, frag 2], blk [.bits 1], blk [.bits 2]] [(0, 0)]

-- Both let escape `0`, `1` and `2`, but give `1` and `2` different handles,
-- so the lists differ and the condition of Q6 fails.
#guard (q6src.escapeCall id []).escaped == [(0, 0), (0, 1), (0, 2)]
#guard (q6tgt.escapeCall id []).escaped == [(0, 0), (0, 2), (0, 1)]

/-! # Reading back the world's reply -/

/-- A traced state in which allocation `0` has the handle 0. -/
def esc0 : TraceState Nat w := st [blk [.bits 1]] [(0, 0)]

-- A pointer of handle 0 reads back as a pointer into `0`; an integer as
-- itself.
#guard (readReply id esc0 [.ptr 0, .int 8] [⟨.ptr 0, .value ⟨some 0, 3⟩⟩, ⟨.int 8, .value 5⟩]).isSome
-- A handle that names no escaped allocation, a value of another type, or a
-- missing value, is a reply the world cannot give.
#guard (readReply id esc0 [.ptr 0] [⟨.ptr 0, .value ⟨some 1, 0⟩⟩]).isNone
#guard (readReply id esc0 [.ptr 0] [⟨.int 8, .value 5⟩]).isNone
#guard (readReply id esc0 [.ptr 0] []).isNone

/-- A pointer of handle 0 reads back as a pointer into allocation `0`. -/
example : readReply id esc0 [.ptr 0] [⟨.ptr 0, .value ⟨some 0, 3⟩⟩] =
    some [⟨.ptr 0, .value ⟨some 0, 3⟩⟩] := rfl

/-! # A poison argument that holds no pointer -/

/-- On a poison integer and on 5, from traced states that refine each other
and from which nothing escaped, both calls let nothing escape, so the rule
is monotone: each way the call on 5 may end is allowed by a way the call on
poison may end. -/
example {s s' : TraceState Nat w} (hS : s ⊑ s') (hs : s.escaped = []) :
    ∀ e', traceExtCall id "g" [⟨.int 32, .value 5⟩] [.int 32] s' e' →
      ∃ e, traceExtCall id "g" [⟨.int 32, .poison⟩] [.int 32] s e ∧
        TraceEnd.Allows (fun vs vs' : List (DVal CoreDialect) => vs ⊑ vs') e e' :=
  traceExtCall_isRefinedBy id (show ([⟨.int 32, .poison⟩] : List (DVal CoreDialect)) ⊑
    [⟨.int 32, .value 5⟩] from ⟨⟨rfl, trivial⟩, trivial⟩) hS
    ((escapeCall_nil s hs).trans (escapeCall_nil s' (hS.2 ▸ hs)).symm) "g" [.int 32]

/-! # Its laws -/

/-- The rule has an outcome from every traced state. -/
example (s : TraceState Nat w) : ∃ vs t s', traceExtCall id "g" q4tgt [.int 32] s (.ok (vs, t, s')) :=
  traceExtCall_exists id "g" q4tgt [.int 32] s

/-! # Axioms -/

/-- info: 'Fir.TraceState.escapeCall_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.TraceState.escapeCall_closed

/-- info: 'Fir.TraceState.escapeCall_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.TraceState.escapeCall_sound

/-- info: 'Fir.Core.traceExtCall_finite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.traceExtCall_finite

/-- info: 'Fir.Core.traceExtCall_isRefinedBy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.traceExtCall_isRefinedBy

/-- info: 'Fir.Core.traceExtCall_types' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.traceExtCall_types

end FirTest.CoreExtCallRule
