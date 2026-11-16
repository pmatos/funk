import Fir.Memory.CanonicalLaws
import Fir.Memory.ExposeLaws

/-!
Tests of the addresses of exposed allocations (#232): which addresses fit
an allocation, what exposing changes, and the canonical layout, with the
fallbacks it takes when the canonical address does not fit.
-/

namespace FirTest.Address

open Fir.Memory

/-- Two allocations of 4 bytes, aligned to 4, the first given the
address 4. -/
def two : Memory 8 := (((Memory.empty.alloc .stack 4 4).2.expose 0 4).alloc .stack 4 4).2

/-- The bounds of the strictest reading for `P`-bit pointers: no
allocation at 0, and every one ending below `2 ^ P`. -/
def hi (P : Nat) : Nat := 2 ^ P - 1

/-! # Which addresses fit -/

-- Below the lower bound, and an address that is not aligned, never fit.
#guard !two.fits 1 (hi 64) 1 0
#guard !two.fits 1 (hi 64) 1 10
-- The live first allocation takes 4 to 8, so the second may not overlap it.
#guard !two.fits 1 (hi 64) 1 4
#guard two.fits 1 (hi 64) 1 8
-- An allocation must end by the upper bound: with 4-bit pointers, 8 + 4 =
-- 12 fits, and 12 + 4 = 16 does not, unless the bound is the loosest.
#guard two.fits 1 (hi 4) 1 8
#guard !two.fits 1 (hi 4) 1 12
#guard two.fits 0 (2 ^ 4) 1 12
-- No address fits an allocation the memory does not have.
#guard !two.fits 1 (hi 64) 2 16

/-! # Exposing -/

-- Exposing keeps the first address an allocation was given.
#guard (two.expose 0 12).addrOf 0 == some 4
#guard (two.expose 1 12).addrOf 1 == some 12
-- It changes no load.
#guard ((two.expose 1 12).load ⟨some 1, 0⟩ 4).toOption == (two.load ⟨some 1, 0⟩ 4).toOption

/-! # The canonical layout -/

-- The second allocation's canonical address is 9 aligned up to 4.
#guard two.bump 1 1 == 12
#guard two.canonical 1 (hi 64) 1 == some 12
-- With 4-bit pointers, 12 + 4 = 16 does not fit, and the layout gives the
-- lowest address that fits: 4 is taken, so 8.
#guard two.canonical 1 (hi 4) 1 == some 8
-- Freed, the first allocation leaves its addresses to the second.
#guard (two.free 0).canonical 1 (hi 4) 1 == some 4
-- Ending by 11, only 4 could fit the second allocation, and the live first
-- allocation takes it; freed, it leaves it.
#guard two.canonical 1 11 1 == none
#guard (two.free 0).canonical 1 11 1 == some 4

/-- Three allocations of 4 bytes exposed at 40, 4 and 28, and a fourth. -/
def four : Memory 8 :=
  let M := (((Memory.empty.alloc .stack 4 4).2.alloc .stack 4 4).2.alloc .stack 4 4).2
  ((((M.expose 0 40).expose 1 4).expose 2 28).alloc .stack 4 4).2

-- The fourth's canonical address, 28, is taken, and the lowest address that
-- fits is 8, after the allocation at 4, not 44, after the first allocation.
#guard four.bump 1 3 == 28
#guard four.canonical 1 (hi 6) 3 == some 8

/-- The canonical layout gives the address that fits. -/
example : two.fits 1 (hi 4) 1 8 = true := Memory.canonical_fits (by decide)

end FirTest.Address
