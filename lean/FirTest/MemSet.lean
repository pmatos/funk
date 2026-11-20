import Fir
import FirRef.Run

/-!
Tests of `memSet`'s rule with memory, run in the state layer over the tree
of choices, the monad that `fir-ref run` computes in. A fill writes copies
of its value's unit: an `i8` filled over four bytes reads back as an `i32`
of four equal bytes, a poison value writes poison units, and units past the
length keep what they held. A length of 0 does nothing, whatever the
pointer is (the human's rulings of 2026-11-18 on #234). A poison pointer
with another length is UB, and so is a length past the allocation: by
`FirRef.memSetFast`, which `fir-ref` runs, at once however long. In memory
1, of 16-bit units, the value is an `i16` and the length counts those
units. A poison length chooses its value: over an allocation of one unit,
an `i1` length has two paths and neither is UB. Then the validation of the
unit width, and the axioms of the obligations that `memSet` meets with
memory and of the fast path.
-/

namespace FirTest.MemSet

open Fir Fir.Core Fir.Memory

/-- Memory 1 has 16-bit units and 32-bit pointers; every other memory has
the default entry: 8-bit units and 64-bit pointers. -/
def lay : Nat → MemLayout := fun n =>
  if n = 1 then { mem := 1, unit := 16, pointer := 32, order := .little } else MemLayout.default

abbrev Mems := Memories Nat (unitsOf lay)

abbrev M := StateT Mems (ChoiceTree Op)

/-- Inside a call, an allocation of `c` units of memory `n`, aligned to 8:
its pointer and the memories after it. -/
def alloc (c n : Nat) : Pointer × Mems :=
  Memories.empty.enter.alloc n .stack c 8

/-- The pointer `k` units past `p`. -/
def at_ (p : Pointer) (k : Int) : Pointer := ⟨p.prov, p.offset + k⟩

/-- The memories after a computation with no result, or the reason for its
UB. -/
def after (c : M (HVector toType ([] : List Ty))) (S : Mems) : Except String Mems :=
  match c S with
  | .pure (_, S') => .ok S'
  | .ub r => .error r
  | _ => .error "no single outcome"

/-- The rule of a fill in memory `n` of a value of `iV`, of a length of
`iW`, from `S`. -/
def fill (n v w : Nat) (p : PoisonOr Pointer) (x : PoisonOr (BitVec v)) (l : PoisonOr (BitVec w))
    (S : Mems) : Except String Mems :=
  after (memSetRule lay id v w n p x l) S

/-- The same fill by `FirRef.memSetFast`, which `fir-ref` runs. -/
def fillFast (n v w : Nat) (p : PoisonOr Pointer) (x : PoisonOr (BitVec v))
    (l : PoisonOr (BitVec w)) (S : Mems) : Except String Mems :=
  after (FirRef.memSetFast lay id v w n p x l) S

/-- A store of an `iW` through `p` in memory `n`. -/
def store (n w : Nat) (v : BitVec w) (p : Pointer) (S : Mems) : Except String Mems :=
  after (storeRule lay id w (some 1) n (.value v) (.value p)) S

/-- The reason for the UB that a computation ends with, if it does. -/
def ubOf {α : Type} : Except String α → Option String
  | .error r => some r
  | .ok _ => none

/-- What a load of an `iW` through `p` in memory `n` gives from `S`. -/
def load (n w : Nat) (p : Pointer) (S : Mems) : Option (PoisonOr (BitVec w)) :=
  match (loadRule lay id w (some 1) n (.value p) : M _) S with
  | .pure (.cons v .nil, _) => some v
  | _ => none

-- Four copies of the byte 0xab read back as an `i32` of four of them.
#guard (do
  let (p, S) := alloc 4 0
  let S ← fill 0 8 64 (.value p) (.value 0xab) (.value 4) S
  pure (load 0 32 p S)).toOption == some (some (.value 0xabababab))

-- A fill of two units leaves the units past them as they were.
#guard (do
  let (p, S) := alloc 4 0
  let S ← store 0 32 0x04030201 p S
  let S ← fill 0 8 8 (.value p) (.value 0xff) (.value 2) S
  pure (load 0 32 p S)).toOption == some (some (.value 0x0403ffff))

-- A poison value writes poison units, and is not UB.
#guard (do
  let (p, S) := alloc 4 0
  let S ← store 0 32 0x04030201 p S
  let S ← fill 0 8 64 (.value p) .poison (.value 4) S
  pure (load 0 32 p S)).toOption == some (some .poison)

-- A length of 0 does nothing, through a poison pointer, a pointer with no
-- provenance, and into a freed allocation.
#guard (fill 0 8 64 .poison (.value 1) (.value 0) (alloc 4 0).2 |>.toOption.isSome)
#guard (fill 0 8 8 (.value ⟨none, 5⟩) (.value 1) (.value 0) (alloc 4 0).2 |>.toOption.isSome)
#guard (fill 0 8 64 (.value (alloc 4 0).1) (.value 1) (.value 0) (alloc 4 0).2.exit
  |>.toOption.isSome)

-- With another length, a poison pointer is UB, and so is a length past the
-- allocation, a pointer with no provenance and a freed allocation, by the
-- rule and by the fast path alike.
#guard ubOf (fill 0 8 64 .poison (.value 1) (.value 1) (alloc 4 0).2) ==
  some "a memset through a poison pointer"
#guard ubOf (fill 0 8 64 (.value (alloc 4 0).1) (.value 1) (.value 5) (alloc 4 0).2) ==
  some "an access out of bounds"
#guard ubOf (fill 0 8 64 (.value (at_ (alloc 4 0).1 (-1))) (.value 1) (.value 2) (alloc 4 0).2) ==
  some "an access out of bounds"
#guard ubOf (fill 0 8 64 (.value ⟨none, 0⟩) (.value 1) (.value 1) (alloc 4 0).2) ==
  some "an access through a pointer without provenance"
#guard ubOf (fill 0 8 64 (.value (alloc 4 0).1) (.value 1) (.value 1) (alloc 4 0).2.exit) ==
  some "an access to a freed allocation"
#guard ubOf (fillFast 0 8 64 .poison (.value 1) (.value 1) (alloc 4 0).2) ==
  some "a memset through a poison pointer"
#guard ubOf (fillFast 0 8 64 (.value (alloc 4 0).1) (.value 1) (.value 5) (alloc 4 0).2) ==
  some "an access out of bounds"
#guard ubOf (fillFast 0 8 64 (.value ⟨none, 0⟩) (.value 1) (.value 1) (alloc 4 0).2) ==
  some "an access through a pointer without provenance"
-- The fast path faults on 2^63 units into an allocation of 4 at once,
-- without building them.
#guard ubOf (fillFast 0 8 64 (.value (alloc 4 0).1) (.value 1) (.value (2 ^ 63)) (alloc 4 0).2) ==
  some "an access out of bounds"
-- It fills as the rule does where the store lands.
#guard (do
  let (p, S) := alloc 4 0
  let S ← fillFast 0 8 64 (.value p) (.value 0xab) (.value 4) S
  pure (load 0 32 p S)).toOption == some (some (.value 0xabababab))

-- In memory 1, of 16-bit units, an `i16` fills one unit per count, and a
-- length of 2 fills an `i32`.
#guard (do
  let (p, S) := alloc 4 1
  let S ← fill 1 16 32 (.value p) (.value 0xbeef) (.value 2) S
  pure (load 1 32 p S)).toOption == some (some (.value 0xbeefbeef))
#guard ubOf (fill 1 16 32 (.value (alloc 4 1).1) (.value 0xbeef) (.value 5) (alloc 4 1).2) ==
  some "an access out of bounds"

-- A poison `i1` length over an allocation of one unit chooses 0 or 1, and
-- neither path is UB.
#guard match (memSetRule lay id 8 1 0 (.value (alloc 1 0).1) (.value 7) .poison : M _)
    (alloc 1 0).2 with
  | .choose 1 .bits k => (k 0 matches .pure _) && (k 1 matches .pure _)
  | _ => false
-- A poison length is UB where some length is.
#guard match (memSetRule lay id 8 2 0 (.value (alloc 1 0).1) (.value 7) .poison : M _)
    (alloc 1 0).2 with
  | .choose 2 .bits k => (k 0 matches .pure _) && (k 1 matches .pure _) && (k 2 matches .ub _)
  | _ => false

/-! # The unit's width

The module's data layout asks that the value of a fill be as wide as a unit
of the pointer's memory.
-/

-- A fill asks its memory's unit width; no other op asks one.
#guard Op.unitWidths (.memSet .nonatomic 16 64 1) == [(1, 16)]
#guard (Op.unitWidths (.store .nonatomic 8 none 0)).isEmpty

-- An `i8` into memory 0 is valid; an `i16` into memory 0, of bytes, is
-- not, and neither is an `i8` into a memory of 16-bit units.
#guard (DataLayout.HasUnits [] (0, 8) : Bool)
#guard !(DataLayout.HasUnits [] (0, 16) : Bool)
#guard !(DataLayout.HasUnits [{ mem := 1, unit := 16, pointer := 32, order := .little }] (1, 8) :
  Bool)
#guard (unitsProblem [] "f" [(0, 8), (0, 16)]).map (·.message) ==
  some "an op writes values of 16 bits into memory 0, whose units have 8 bits"
#guard (unitsProblem [] "f" [(0, 8), (0, 8)]).isNone

/-! # Axioms -/

/-- info: 'Fir.Core.memSet_memTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.memSet_memTotal

/-- info: 'Fir.Core.memSet_memMonotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.memSet_memMonotone

/-- info: 'Fir.Core.memSet_readsNot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.memSet_readsNot

/-- info: 'Fir.Core.memSet_writesNot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.memSet_writesNot

/-- info: 'Fir.Core.memSet_allocatesNot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.memSet_allocatesNot

/-- info: 'Fir.Core.memSet_finitelyMany' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.memSet_finitelyMany

/-- info: 'Fir.Core.memSet_memPropagates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.memSet_memPropagates

/-- info: 'Fir.Core.memSet_memReturnsOnDefined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.memSet_memReturnsOnDefined

/-- info: 'Fir.Core.memSet_makesNoPoison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.memSet_makesNoPoison

/-- info: 'FirRef.memTreeDenote_eq_memTreeFast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirRef.memTreeDenote_eq_memTreeFast

end FirTest.MemSet
