import Fir.Memory.PolicyLaws

/-!
Tests of exposing a pointer in the memories of a run (#232): the integer it
gives under the canonical layout and under other address policies, the
fallback when a policy proposes an address that may not be given, a second
exposure, the wrap at the pointer width, UB when no address fits, and the
addresses of freed allocations.
-/

namespace FirTest.Expose

open Fir Fir.Memory

/-- Memories of 8-bit units, by number. -/
abbrev Mems := Memories Nat fun _ => 8

/-- One allocation of 4 bytes, aligned to 4, in memory 0. -/
def one : Mems := ((Memories.empty : Mems).alloc 0 .stack 4 4).2

/-- The integer that exposing `p` of memory 0 gives under the policy `g`,
with `P`-bit pointers, if any. -/
def int (S : Mems) (g : Policy) (P : Nat) (p : Pointer) : Option Nat :=
  (S.expose 0 g P p).map (·.1.toNat)

/-- The policy that proposes the address `y` for every allocation. -/
def propose (y : Nat) : Policy := fun _ _ => some y

-- The canonical layout gives the first allocation the address 4, and a
-- pointer gives that address plus its offset.
#guard int one Policy.canonical 64 ⟨some 0, 0⟩ == some 4
#guard int one Policy.canonical 64 ⟨some 0, 3⟩ == some 7
-- A policy's proposal that fits is the address given.
#guard int one (propose 8) 64 ⟨some 0, 0⟩ == some 8
-- A proposal that does not fit, misaligned or at 0, falls back to the
-- canonical address.
#guard int one (propose 5) 64 ⟨some 0, 0⟩ == some 4
#guard int one (propose 0) 64 ⟨some 0, 0⟩ == some 4
-- An allocation keeps the first address it is given, whatever the policy.
#guard ((one.expose 0 (propose 8) 64 ⟨some 0, 0⟩).bind fun r =>
  int r.2 (propose 16) 64 ⟨some 0, 1⟩) == some 9
-- The integer wraps at the pointer width: below 0, and past `2 ^ P`.
#guard int one Policy.canonical 64 ⟨some 0, -8⟩ == some (2 ^ 64 - 4)
#guard int one Policy.canonical 8 ⟨some 0, 300⟩ == some 48
-- A pointer with no provenance gives its offset.
#guard int one Policy.canonical 64 ⟨none, 42⟩ == some 42
-- No address fits 300 bytes with 8-bit pointers, below `2 ^ 8 - 1`: UB.
#guard int ((Memories.empty : Mems).alloc 0 .stack 300 1).2 Policy.canonical 8 ⟨some 0, 0⟩ == none
-- A pointer whose allocation the memory does not have gives its offset.
#guard int one Policy.canonical 64 ⟨some 1, 7⟩ == some 7

/-- The memories after exposing the allocation `a` of memory 0 under the
policy that proposes `y`, if it has an outcome. -/
def exposeAt (S : Mems) (a y : Nat) : Option Mems :=
  (S.expose 0 (propose y) 64 ⟨some a, 0⟩).map (·.2)

/-- Two allocations of 4 bytes, aligned to 4, the first exposed at 4. -/
def two : Option Mems := exposeAt ((one.alloc 0 .stack 4 4).2) 0 4

-- A proposal that overlaps a live allocation with an address does not fit,
-- and the second allocation gets its canonical address, 12, past the gap.
#guard (two.bind fun S => int S (propose 4) 64 ⟨some 1, 0⟩) == some 12
#guard (two.bind fun S => int S (propose 8) 64 ⟨some 1, 0⟩) == some 8
-- A live allocation may get the address of a freed one.
#guard ((exposeAt one 0 4).bind fun S =>
  int ((S.free 0 0).alloc 0 .stack 4 4).2 (propose 4) 64 ⟨some 1, 0⟩) == some 4
-- A freed allocation may get the address of a live one, as a dangling
-- pointer to a reused stack slot does.
#guard ((exposeAt (((one.alloc 0 .stack 4 4).2).free 0 0) 1 4).bind fun S =>
  int S (propose 4) 64 ⟨some 0, 0⟩) == some 4
-- A live one may not: the proposal falls back to the canonical address.
#guard ((exposeAt ((one.alloc 0 .stack 4 4).2) 1 4).bind fun S =>
  int S (propose 4) 64 ⟨some 0, 0⟩) == some 8

end FirTest.Expose
