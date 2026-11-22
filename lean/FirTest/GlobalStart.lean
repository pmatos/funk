import FirTest.Global

/-!
Tests of the memories a run starts with (#237): one allocation of kind
`global` for each global of the run's own table, in the memory of its
number, with its alignment and constness, holding its initializer's units
and then zeros up to its size (the human's ruling of 2026-11-20 on #237,
Q1); a store to a constant global's block faults, and a load reads it
(Q2); a nested module's globals are its own table's, not the host's (Q3).
-/

namespace FirTest

open Fir Memory

/-- What a test sees of a unit: its bits as a number, `p` for poison, or a
fragment as its memory, its pointer's id and offset, and its index. -/
def seeUnit {u : Nat} : MemUnit u → String
  | .bits b => toString b.toNat
  | .poison => "p"
  | .frag m p i => s!"{m}:{p.prov}+{p.offset}#{i}"

/-- What a test sees of a block: its kind, alignment, constness and
units. -/
abbrev SeenBlock := AllocKind × Nat × Bool × List String

/-- The memories that a run of a function of the table `t` of `M` starts
with, each memory with its entry in `M`'s data layout, named by its
number. -/
def startIn (M : Module CoreDialect) (t : SymbolTable CoreDialect) :
    Memories Nat (unitsOf M.layout.entry) :=
  RunItems.start CoreDialect M.layout.entry id (RunItems.ofTable M.layout t)

/-- The blocks of the memory `n` that a run of a function of the `k`th
table of the module text `src`, its own first, starts with. -/
def startBlocks (src : String) (k n : Nat) : Option (List SeenBlock) :=
  match parseCore src with
  | .ok M => M.tables[k]?.map fun t =>
    ((startIn M t).mem n).blocks.map fun b => (b.kind, b.align, b.const, b.units.map seeUnit)
  | .error _ => none

/-- How a store of one unit of bits to the start of the allocation `a` of
the memory `n`, at the start of a run of the module text `src`, ends:
`ok`, or the reason of its fault. -/
def storeAt (src : String) (n a : Nat) : String :=
  match parseCore src with
  | .ok M =>
    match ((startIn M M.table).mem n).store ⟨some a, 0⟩ [.bits 1] with
    | .ok _ => "ok"
    | .error f => f.reason
  | .error _ => "no parse"

/-- A module with the layout line `l` and the globals of the attributes
`gs`, named `@a`, `@b`, `@c` and so on. -/
def globsIn (l : String) (gs : List String) : String :=
  "layout " ++ l ++ "\n\n" ++ oneFunc (String.join (gs.zipIdx.map fun (g, i) =>
    "global @" ++ String.singleton (Char.ofNat (97 + i)) ++ "() " ++ g ++ " {\n}\n\n"))

/-! # Units, zeros and constness -/

-- A global holds its units, then zeros up to its size (Q1), in a constant
-- block of kind `global` with its alignment.
#guard startBlocks (glob "size(8) align(1) const units(104, 105, 0)") 0 0 ==
  some [(.global, 1, true, ["104", "105", "0", "0", "0", "0", "0", "0"])]
-- With no initializer it holds zeros, and is not constant.
#guard startBlocks (glob "size(4) align(4)") 0 0 ==
  some [(.global, 4, false, ["0", "0", "0", "0"])]
-- `zeros(n)` gives zeros, and the units after them are the next pieces'.
#guard startBlocks (glob "size(4) align(1) zeros(2) units(7)") 0 0 ==
  some [(.global, 1, false, ["0", "0", "7", "0"])]
-- A global of no units is an empty block.
#guard startBlocks (glob "size(0) align(1)") 0 0 == some [(.global, 1, false, [])]
-- A module with no global starts from empty memories.
#guard startBlocks (oneFunc "func @f() {\n^e:\n  ret @0\n}\n") 0 0 == some []

/-! # Addresses -/

-- Globals take the ids of their memory in the table's order, and an address
-- takes the eight fragments of a pointer of memory 0 to its global, plus its
-- offset, as a store of that pointer writes them.
#guard startBlocks (globs "size(1) align(1) units(9)" "size(16) align(8) addr(@a) addr(@a, 2)")
    0 0 ==
  some [(.global, 1, false, ["9"]),
    (.global, 8, false, (List.range 8).map (s!"0:(some 0)+0#{·}") ++
      (List.range 8).map (s!"0:(some 0)+2#{·}"))]
-- A global may hold its own address.
#guard startBlocks (glob "size(8) align(8) addr(@g, 4)") 0 0 ==
  some [(.global, 8, false, (List.range 8).map (s!"0:(some 0)+4#{·}"))]
-- The fragments decode as the pointer, as a load of a pointer reads them.
#guard (match parseCore (glob "size(8) align(8) addr(@g, 4)") with
  | .ok M => (((startIn M M.table).mem 0).blocks[0]?.map fun b =>
      decodePtr 0 8 .little b.units) == some (.value ⟨some 0, 4⟩)
  | .error _ => false)

-- In a memory of 16-bit units with 32-bit pointers, a unit holds 16 bits.
-- A pointer of memory 0, of 64 bits, takes four of them there, and one of
-- memory 1 two. Each memory numbers its own globals: `@c` is the second
-- of memory 0, and `@b` the first of memory 1.
#guard startBlocks (globsIn mem16g ["size(1) align(1) units(1)",
    "memory(1) size(8) align(2) units(65535) addr(@c, 1) addr(@b)", "size(2) align(1) units(2, 3)"])
    0 1 ==
  some [(.global, 2, false, ["65535"] ++ (List.range 4).map (s!"0:(some 1)+1#{·}") ++
    (List.range 2).map (s!"1:(some 0)+0#{·}") ++ ["0"])]
#guard startBlocks (globsIn mem16g ["size(1) align(1) units(1)",
    "memory(1) size(8) align(2) units(65535) addr(@c, 1) addr(@b)", "size(2) align(1) units(2, 3)"])
    0 0 ==
  some [(.global, 1, false, ["1"]), (.global, 1, false, ["2", "3"])]

/-! # Writing a constant global -/

-- A store to a constant global faults: writing it is UB when the write runs
-- (Q2). A store to a global that is not constant does not.
#guard storeAt (glob "size(4) align(4) const units(1, 0, 0, 0)") 0 0 ==
  "a store to a constant allocation"
#guard storeAt (glob "size(4) align(4) units(1, 0, 0, 0)") 0 0 == "ok"
-- A load of a constant global reads its units.
#guard (match parseCore (glob "size(4) align(4) const units(5, 0, 0, 0)") with
  | .ok M => (((startIn M M.table).mem 0).load ⟨some 0, 0⟩ 2).toOption.map (·.map seeUnit) ==
      some ["5", "0"]
  | .error _ => false)
-- A store that is out of bounds faults as such, constant or not.
#guard (match parseCore (glob "size(1) align(1) const") with
  | .ok M => (((startIn M M.table).mem 0).store ⟨some 0, 1⟩ [.bits 1]).toOption.isNone &&
      match ((startIn M M.table).mem 0).store ⟨some 0, 1⟩ [.bits 1] with
      | .error f => f == .outOfBounds
      | .ok _ => false
  | .error _ => false)

/-! # A run holds its own table's globals -/

/-- A host with a global, and a nested module with one of its own. -/
def hostAndDev : String :=
  oneFunc ("global @h() size(1) align(1) units(7) {\n}\n\n" ++
    "module @dev() {\n  global @g() size(2) align(2) units(1, 2) {\n  }\n\n}\n")

-- A run of a host function holds the host's global only, and a run of a
-- function of the nested module holds that module's only (Q3).
#guard startBlocks hostAndDev 0 0 == some [(.global, 1, false, ["7"])]
#guard startBlocks hostAndDev 1 0 == some [(.global, 2, false, ["1", "2"])]

end FirTest
