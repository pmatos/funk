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

/-! # Which addresses fit -/

-- The address 0 never fits, and neither does one that is not aligned.
#guard !two.fits 64 1 0
#guard !two.fits 64 1 10
-- The live first allocation takes 4 to 8, so the second may not overlap it.
#guard !two.fits 64 1 4
#guard two.fits 64 1 8
-- An allocation must end below 2 ^ P: with 4-bit pointers, 8 + 4 = 12 < 16
-- fits, and 12 + 4 = 16 does not.
#guard two.fits 4 1 8
#guard !two.fits 4 1 12
-- No address fits an allocation the memory does not have.
#guard !two.fits 64 2 16

/-! # Exposing -/

-- Exposing keeps the first address an allocation was given.
#guard (two.expose 0 12).addrOf 0 == some 4
#guard (two.expose 1 12).addrOf 1 == some 12
-- It changes no load.
#guard ((two.expose 1 12).load ⟨some 1, 0⟩ 4).toOption == (two.load ⟨some 1, 0⟩ 4).toOption

/-! # The canonical layout -/

-- The second allocation's canonical address is 9 aligned up to 4.
#guard two.bump 1 == 12
#guard two.canonical 64 1 == some 12
-- With 4-bit pointers, 12 + 4 = 16 does not fit, and the layout falls back
-- to the first address after the first allocation that fits.
#guard two.canonical 4 1 == some 8
-- Freed, the first allocation leaves its addresses to the second, and the
-- layout falls back to the first multiple of 4 from 1.
#guard (two.free 0).canonical 4 1 == some 4
-- With 3-bit pointers nothing fits the second allocation beside the first.
#guard two.canonical 3 1 == none

/-- The canonical layout gives the address that fits. -/
example : two.fits 4 1 8 = true := Memory.canonical_fits (by decide)

end FirTest.Address
