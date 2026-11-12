import Fir

/-!
Tests of values in units: integers and pointers encoded in a memory's units
at each byte order, decoded back, odd widths with their zero padding and
the padding ignored, poison, punned and partial units, the sizes of the
core's types, and a value stored to memory and loaded back.
-/

namespace FirTest.MemoryEncode

open Fir Fir.Memory

def bs (xs : List Nat) : List (MemUnit 8) := xs.map fun x => .bits (BitVec.ofNat 8 x)

def p : Pointer := ⟨some 3, 5⟩
def q : Pointer := ⟨some 4, 0⟩

-- An `i32` in bytes: least significant first when little, reversed when big.
#guard encodeInt 8 .little (.value 0x11223344#32) == bs [0x44, 0x33, 0x22, 0x11]
#guard encodeInt 8 .big (.value 0x11223344#32) == bs [0x11, 0x22, 0x33, 0x44]
#guard decodeInt 8 32 .little (bs [0x44, 0x33, 0x22, 0x11]) == .value 0x11223344#32
#guard decodeInt 8 32 .big (bs [0x44, 0x33, 0x22, 0x11]) == .value 0x44332211#32

-- An `i32` in 16-bit units takes two.
#guard encodeInt 16 .little (.value 0x11223344#32) == [.bits 0x3344, .bits 0x1122]

-- Odd widths take whole units, with zero padding: `i20` in three bytes,
-- `i1` in one.
#guard encodeInt 8 .little (.value 0xABCDE#20) == bs [0xDE, 0xBC, 0x0A]
#guard encodeInt 8 .big (.value 0xABCDE#20) == bs [0x0A, 0xBC, 0xDE]
#guard encodeInt 8 .little (.value 1#1) == bs [0x01]

-- A load ignores the extra bits, whatever they hold: `i1` from 0xFF is 1.
#guard decodeInt 8 1 .little (bs [0xFF]) == .value 1#1
#guard decodeInt 8 1 .little (bs [0xFE]) == .value 0#1
#guard decodeInt 8 20 .little (bs [0xDE, 0xBC, 0xFA]) == .value 0xABCDE#20

-- Poison takes as many units, and one poison unit makes the integer poison.
#guard encodeInt 8 .little (.poison : PoisonOr (BitVec 20)) == List.replicate 3 .poison
#guard decodeInt 8 20 .little (List.replicate 3 .poison) == .poison
#guard decodeInt 8 20 .little (bs [0xDE, 0xBC] ++ [.poison]) == .poison

-- Units of the wrong number decode to poison.
#guard decodeInt 8 32 .little (bs [0x44, 0x33, 0x22]) == .poison

-- A pointer is its fragments, in the byte order, and decodes back.
#guard (encodePtr 2 .little (.value p) : List (MemUnit 8)) == [.frag p 0, .frag p 1]
#guard (encodePtr 2 .big (.value p) : List (MemUnit 8)) == [.frag p 1, .frag p 0]
#guard decodePtr 8 .little (encodePtr (u := 8) 8 .little (.value p)) == .value p
#guard decodePtr 8 .big (encodePtr (u := 8) 8 .big (.value p)) == .value p
#guard decodePtr 8 .little (encodePtr (u := 8) 8 .little .poison) == .poison

-- Fragments out of order, of two pointers, or partly overwritten are not a
-- pointer.
#guard decodePtr 2 .big (encodePtr (u := 8) 2 .little (.value p)) == .poison
#guard decodePtr 2 .little ([.frag p 0, .frag q 1] : List (MemUnit 8)) == .poison
#guard decodePtr 2 .little ([.frag p 0] ++ bs [0x2a]) == .poison

-- Punned loads give poison: an integer from fragments, a pointer from bits.
#guard decodeInt 8 64 .little (encodePtr 8 .little (.value p)) == .poison
#guard decodePtr 8 .little (encodeInt 8 .little (.value 0x2a#64)) == .poison

-- The sizes of the core's types: `ptr` in the default memory takes 8 bytes,
-- and a 32-bit pointer of memory 1 takes 4 of them, or 2 units of 16 bits.
def layout : DataLayout := [{ mem := 1, unit := 16, pointer := 32, order := .little }]

#guard Core.Ty.units? [] 8 (.int 20) == some 3
#guard Core.Ty.units? [] 8 (.ptr 0) == some 8
#guard Core.Ty.units? layout 8 (.ptr 1) == some 4
#guard Core.Ty.units? layout 16 (.ptr 1) == some 2
#guard Core.Ty.units? [] 8 (.ptr 1) == none
#guard Core.Ty.units? [] 8 (.float 8 23) == none

-- A value stored to memory and loaded back decodes to itself.
def m : Pointer × Memory 8 := Memory.empty.alloc .stack 16

#guard ((m.2.store m.1 (encodeInt 8 .little (.value 0xABCDE#20)) >>= fun M =>
    M.load m.1 3).toOption.map (decodeInt 8 20 .little)) == some (.value 0xABCDE#20)
#guard ((m.2.store m.1 (encodePtr 8 .little (.value p)) >>= fun M =>
    M.load m.1 8).toOption.map (decodePtr 8 .little)) == some (.value p)

end FirTest.MemoryEncode
