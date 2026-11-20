import Fir.Memory.ResolverLaws

/-!
Tests of turning an integer back into a pointer in the memories of a run
(#232): the memory model's own pick, a resolver's proposal, a resolver that
picks differently at each call, an address one past an allocation's end,
freed and unexposed allocations, an address that no allocation holds, and
a round trip through an exposure.
-/

namespace FirTest.FromAddr

open Fir Fir.Memory

/-- Memories of 8-bit units, by number. -/
abbrev Mems := Memories Nat fun _ => 8

/-- The policy that proposes the address `y` for every allocation. -/
def propose (y : Nat) : Policy := fun _ _ => some y

/-- The memories after exposing the allocation `a` of memory 0 at `y`. -/
def exposeAt (S : Mems) (a y : Nat) : Mems :=
  ((S.expose 0 (propose y) 64 ⟨some a, 0⟩).map (·.2)).getD S

/-- Two allocations of 4 bytes in memory 0: the first exposed at 4, the
second at 8, where the first ends. -/
def two : Mems :=
  exposeAt (exposeAt ((((Memories.empty : Mems).alloc 0 .stack 4 4).2).alloc 0 .stack 4 4).2 0 4) 1 8

/-- The resolver that proposes `a` at every call. -/
def toAlloc (a : AllocId) : Resolver := fun _ _ _ => some a

/-- The pointer that the 64-bit integer `z` of memory 0 becomes. -/
def back (S : Mems) (k : Resolver) (z : Nat) : Pointer := (S.fromAddr 0 k 64 (BitVec.ofNat 64 z)).1

-- The memory model's pick: the allocation whose units hold the address.
#guard back two Resolver.canonical 5 == ⟨some 0, 1⟩
#guard back two Resolver.canonical 11 == ⟨some 1, 3⟩
-- At 8, the first allocation's end and the second's start, it picks the
-- one whose units hold 8.
#guard back two Resolver.canonical 8 == ⟨some 1, 0⟩
-- A resolver may pick the other one: 8 is the first allocation's end.
#guard back two (toAlloc 0) 8 == ⟨some 0, 4⟩
-- One past the second allocation's end is its end.
#guard back two Resolver.canonical 12 == ⟨some 1, 4⟩
-- A proposal that does not hold the address falls back to the pick.
#guard back two (toAlloc 0) 11 == ⟨some 1, 3⟩
#guard back two (toAlloc 7) 5 == ⟨some 0, 1⟩
-- An address that no allocation holds gives a pointer with no provenance,
-- and a load through it is UB.
#guard back two Resolver.canonical 100 == ⟨none, 100⟩
#guard back two Resolver.canonical 3 == ⟨none, 3⟩
#guard ((two.load 0 (back two Resolver.canonical 100) 1 1).toOption.isNone)

/-- The resolver that proposes the first allocation at the call numbered 0
and the second at every later call. -/
def perCall : Resolver := fun c _ _ => if c = 0 then some 0 else some 1

-- Each call counts, and a resolver may pick differently at each one: two
-- calls on the address 8 in the same memories give pointers of different
-- allocations, as question A of #232 asks.
#guard (two.fromAddr 0 perCall 64 8).2.rebuilds == 1
#guard (two.fromAddr 0 perCall 64 8).1 == ⟨some 0, 4⟩
#guard ((two.fromAddr 0 perCall 64 8).2.fromAddr 0 perCall 64 8).1 == ⟨some 1, 0⟩
-- Through the first, the unit at 7 loads; through the second, the unit at 8.
#guard ((two.load 0 ⟨some 0, 3⟩ 1 1).toOption.isSome)
#guard ((two.load 0 ⟨some 1, 0⟩ 1 1).toOption.isSome)

-- A freed allocation never counts, even when a resolver proposes it.
#guard back (two.free 0 0) (toAlloc 0) 5 == ⟨none, 5⟩
#guard back (two.free 0 0) (toAlloc 0) 8 == ⟨some 1, 0⟩
-- An allocation with no address never counts.
#guard back (((Memories.empty : Mems).alloc 0 .stack 4 4).2) (toAlloc 0) 0 == ⟨none, 0⟩
-- Another memory's allocations never count.
#guard (two.fromAddr 1 Resolver.canonical 64 5).1 == ⟨none, 5⟩

-- A round trip: exposing a pointer and turning the integer back gives the
-- pointer again.
#guard (((Memories.empty : Mems).alloc 0 .stack 4 4).2.expose 0 Policy.canonical 64
  ⟨some 0, 3⟩).map (fun r => (r.2.fromAddr 0 Resolver.canonical 64 r.1).1) == some ⟨some 0, 3⟩

end FirTest.FromAddr
