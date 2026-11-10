import Fir

/-!
Tests of the memory model on a memory of 8-bit units: a store and the load
after it, fresh memory, other allocations, and each fault of an access, in
order: no provenance, a freed allocation, and an access out of bounds.
-/

namespace FirTest.Memory

open Fir.Memory

/-- Results of accesses compare by their result or their fault. -/
instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error e, .error f => e == f
    | _, _ => false

/-- A memory with one stack allocation of four bytes, and its pointer. -/
def m1 : Pointer × Memory 8 := Memory.empty.alloc .stack 4

/-- `m1` with a heap allocation of two bytes after it, and its pointer. -/
def m2 : Pointer × Memory 8 := m1.2.alloc .heap 2

def b1 : MemUnit 8 := .bits 0x2a
def b2 : MemUnit 8 := .bits 0x07

-- Fresh memory holds poison, and each allocation gets the next id.
#guard m1.2.load m1.1 4 == .ok (List.replicate 4 .poison)
#guard m1.1 == ⟨some 0, 0⟩ && m2.1 == ⟨some 1, 0⟩

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
    let M ← m2.2.store ⟨some 1, 0⟩ [.frag m1.1 0, .frag m1.1 1]
    M.load m2.1 2) == .ok [.frag m1.1 0, .frag m1.1 1]

-- Each fault of an access.
#guard m2.2.load ⟨none, 0⟩ 1 == .error .noProvenance
#guard m2.2.load ⟨some 2, 0⟩ 1 == .error .noProvenance
#guard (m2.2.free 0).load m1.1 1 == .error .freed
#guard (m2.2.free 0).load m2.1 2 == .ok [.poison, .poison]
#guard m2.2.load ⟨some 0, 3⟩ 2 == .error .outOfBounds
#guard m2.2.load ⟨some 0, -1⟩ 1 == .error .outOfBounds
#guard m2.2.store ⟨some 1, 1⟩ [b1, b2] == .error .outOfBounds
#guard m2.2.load ⟨some 0, 4⟩ 0 == .ok []

/-- The laws hold of the example: a load after a store gives what was
stored. -/
example : ∀ M, m2.2.store ⟨some 0, 1⟩ [b1, b2] = .ok M →
    M.load ⟨some 0, 1⟩ 2 = .ok [b1, b2] :=
  fun _ h => Memory.load_store_same h

end FirTest.Memory
