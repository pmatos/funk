import Fir

/-!
Tests of the memory model on a memory of 8-bit units: a store and the load
after it, fresh memory, other allocations, and each fault of an access, in
order: no provenance, a freed allocation, and an access out of bounds. Then
the table of the memories of a run: it holds each memory once, however many
times the run replaces it.
-/

namespace FirTest.Memory

open Fir.Memory

deriving instance BEq for Except

/-- A memory with one stack allocation of four bytes, aligned to two, and
its pointer. -/
def m1 : Pointer × Memory 8 := Memory.empty.alloc .stack 4 2

/-- `m1` with a heap allocation of two bytes after it, aligned to eight, and
its pointer. -/
def m2 : Pointer × Memory 8 := m1.2.alloc .heap 2 8

def b1 : MemUnit 8 := .bits 0x2a
def b2 : MemUnit 8 := .bits 0x07

-- Fresh memory holds poison, and each allocation gets the next id.
#guard m1.2.load m1.1 4 == .ok (List.replicate 4 .poison)
#guard m1.1 == ⟨some 0, 0⟩ && m2.1 == ⟨some 1, 0⟩

-- Each allocation records the size and the alignment it was allocated with.
#guard m2.2.blocks.map (fun b => (b.units.length, b.align)) == [(4, 2), (2, 8)]

-- A store and the load after it, of units in the middle of the block.
#guard (do
    let M ← m2.2.store ⟨some 0, 1⟩ [b1, b2]
    M.load m1.1 4) == .ok [.poison, b1, b2, .poison]

-- A store leaves the other allocation as it was.
#guard (do
    let M ← m2.2.store ⟨some 0, 0⟩ [b1, b1, b1, b1]
    M.load m2.1 2) == .ok [.poison, .poison]

-- A pointer stored unit by unit keeps its fragments.
#guard (do
    let M ← m2.2.store ⟨some 1, 0⟩ [.frag 0 m1.1 0, .frag 0 m1.1 1]
    M.load m2.1 2) == .ok [.frag 0 m1.1 0, .frag 0 m1.1 1]

-- Each fault of an access.
#guard m2.2.load ⟨none, 0⟩ 1 == .error .noProvenance
#guard m2.2.load ⟨some 2, 0⟩ 1 == .error .noProvenance
#guard (m2.2.free 0).load m1.1 1 == .error .freed
#guard (m2.2.free 0).load m2.1 2 == .ok [.poison, .poison]
#guard m2.2.load ⟨some 0, 3⟩ 2 == .error .outOfBounds
#guard m2.2.load ⟨some 0, -1⟩ 1 == .error .outOfBounds
#guard m2.2.store ⟨some 1, 1⟩ [b1, b2] == .error .outOfBounds
#guard m2.2.load ⟨some 0, 4⟩ 0 == .ok []
#guard m2.2.store ⟨none, 0⟩ [b1] == .error .noProvenance
#guard (m2.2.free 0).store m1.1 [b1] == .error .freed

-- When several faults apply, the first in the order of `locate` wins: a
-- freed allocation accessed out of bounds is `freed`.
#guard (m2.2.free 0).load ⟨some 0, 9⟩ 1 == .error .freed

-- A pointer that names an id not yet allocated faults, and reaches the
-- allocation that later takes the id: provenance comes from allocations.
#guard Memory.empty.load (u := 8) ⟨some 0, 0⟩ 1 == .error .noProvenance

-- Freeing never faults: a second free, or a free of an id the memory does
-- not have, changes nothing.
#guard ((m2.2.free 0).free 0).blocks == (m2.2.free 0).blocks
#guard (m2.2.free 7).blocks == m2.2.blocks

/-- The laws hold of the example: a load after a store gives what was
stored. -/
example : ∀ M, m2.2.store ⟨some 0, 1⟩ [b1, b2] = .ok M →
    M.load ⟨some 0, 1⟩ 2 = .ok [b1, b2] :=
  fun _ h => Memory.load_store_same h

/-! # The table of the memories of a run -/

/-- Memories named by `Bool`, of 8-bit units. -/
abbrev Two := Memories Bool (fun _ => 8)

/-- `n` allocations of one unit, alternating between the two memories, then
a free of each allocation of the memory `true`. -/
def churn (n : Nat) : Two :=
  let S := (List.range n).foldl (fun S i => (S.alloc (i % 2 == 0) .heap 1 1).2) Memories.empty
  (List.range n).foldl (fun S a => S.free true a) S

-- Each memory is in the table once, after thousands of replacements, and
-- each holds its own allocations: the frees of `true` reach only `true`.
#guard (churn 4000).table.length == 2
#guard ((churn 4000).mem true).blocks.length == 2000
#guard ((churn 4000).mem true).blocks.all (!·.live)
#guard ((churn 4000).mem false).blocks.all (·.live)
#guard (Memories.empty : Two).table.isEmpty && ((Memories.empty : Two).mem false).blocks.isEmpty

end FirTest.Memory
