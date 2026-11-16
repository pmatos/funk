import Fir

/-!
Tests of the copy of units (#234) on memories of 8-bit units: a pointer
copied unit by unit keeps its fragments, and loads back as the same pointer;
poison and fresh units are copied as poison; part of a pointer is copied as
its fragments alone; overlapping ranges are copied from what the source
held before, in both directions; another memory is left as it was; and a
copy faults as its load does, then as its store does.
-/

namespace FirTest.MemoryCopy

open Fir Fir.Memory

deriving instance BEq for Except

/-- Memories named by `Bool`, of 8-bit units. -/
abbrev Two := Memories Bool (fun _ => 8)

def b1 : MemUnit 8 := .bits 0x2a
def b2 : MemUnit 8 := .bits 0x07

/-- Two allocations of the memory `false`, of four and eight units, and one of
the memory `true`, of two. -/
def S0 : Two :=
  let S := (Memories.empty.alloc false .stack 4 1).2
  let S := (S.alloc false .stack 8 1).2
  (S.alloc true .stack 2 1).2

def p0 : Pointer := ⟨some 0, 0⟩
def p1 : Pointer := ⟨some 1, 0⟩

/-- A pointer's two fragments, as a store of `p0` in memory `false` would
leave them in a memory of 16-bit pointers. -/
def frags : List (MemUnit 8) := [.frag 0 p0 0, .frag 0 p0 1]

/-- `S0` with `b1`, `b2` and `p0`'s fragments in its first allocation. -/
def S1 : Except Fault Two := S0.store false p0 ([b1, b2] ++ frags) 1

/-- What the first `n` units of the allocation `a` of the memory `false` hold
after `S`. -/
def units (S : Except Fault Two) (a : Nat) (n : Nat) : Except Fault (List (MemUnit 8)) :=
  S.bind fun S => S.load false ⟨some a, 0⟩ n 1

-- A pointer copied unit by unit keeps its fragments, and with them its
-- provenance, so a load of a pointer from the copy decodes `p0` again.
#guard units (S1.bind (·.copy false p1 ⟨some 0, 2⟩ 2 1 1)) 1 2 == .ok frags
#guard (units (S1.bind (·.copy false p1 ⟨some 0, 2⟩ 2 1 1)) 1 2).map
  (decodePtr (u := 8) 0 2 .little) == .ok (.value p0)

-- Part of a pointer is copied as its fragment alone, which loads back as
-- poison.
#guard units (S1.bind (·.copy false p1 ⟨some 0, 3⟩ 1 1 1)) 1 1 == .ok [.frag 0 p0 1]
#guard (units (S1.bind (·.copy false p1 ⟨some 0, 3⟩ 1 1 1)) 1 2).map
  (decodePtr (u := 8) 0 2 .little) == .ok .poison

-- Fresh units are poison, and a copy of them is poison.
#guard units (S1.bind (·.copy false ⟨some 1, 4⟩ ⟨some 1, 0⟩ 4 1 1)) 1 8 ==
  .ok (List.replicate 8 .poison)

-- A copy writes the units its load gave: overlapping ranges get what the
-- source held before the copy, moving forward and backward alike.
#guard units (S1.bind (·.copy false ⟨some 0, 1⟩ p0 3 1 1)) 0 4 == .ok [b1, b1, b2, .frag 0 p0 0]
#guard units (S1.bind (·.copy false p0 ⟨some 0, 1⟩ 3 1 1)) 0 4 ==
  .ok [b2, .frag 0 p0 0, .frag 0 p0 1, .frag 0 p0 1]

-- A copy of a range onto itself changes nothing.
#guard units (S1.bind (·.copy false p0 p0 4 1 1)) 0 4 == units S1 0 4

-- A copy reaches no other memory.
#guard (S1.bind fun S => (S.copy false p1 p0 4 1 1).bind fun S' => S'.load true p0 2 1) ==
  .ok [.poison, .poison]

-- A copy faults as its load does first, then as its store does.
#guard (S1.bind (·.copy false p1 ⟨some 0, 2⟩ 4 1 1)).map (fun _ => ()) == .error .outOfBounds
#guard (S1.bind (·.copy false ⟨none, 0⟩ ⟨some 0, 9⟩ 1 1 1)).map (fun _ => ()) ==
  .error .outOfBounds
#guard (S1.bind (·.copy false ⟨none, 0⟩ p0 1 1 1)).map (fun _ => ()) == .error .noProvenance
#guard (S1.bind (·.copy false ⟨some 1, 7⟩ p0 2 1 1)).map (fun _ => ()) == .error .outOfBounds
#guard (S1.bind (·.copy false ⟨some 1, 1⟩ p0 2 1 2)).map (fun _ => ()) == .error .misaligned

/-- The laws hold of the example: a copy of units, in the state layer, ends
with the memories that `Memories.copy` gives. -/
example (S S' : Two) (h : S.copy false p1 p0 2 1 1 = .ok S') :
    copyUnits (m := StateT Two SetM) false p1 p0 2 1 1 S (.ok ((), S')) :=
  (copyUnits_apply false p1 p0 2 1 1 S _).2 (.inl ⟨S', h, rfl⟩)

end FirTest.MemoryCopy
