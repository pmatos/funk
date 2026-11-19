import Fir.Memory.PolicyLaws

/-!
Tests of exposing a pointer in the memories of a run (#232): the integer it
gives under the canonical layout and under other address policies, the
fallback when a policy proposes an address that does not fit, a second
exposure, the wrap at the pointer width, and UB when no address fits.
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
-- A pointer whose allocation the memory does not have has no address.
#guard int one Policy.canonical 64 ⟨some 1, 0⟩ == none

end FirTest.Expose
