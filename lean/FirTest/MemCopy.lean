import Fir

/-!
Tests of `memCopy`'s rule with memory, run in the state layer over the tree
of choices, the monad that `fir-ref run` computes in. A copy or a move
carries units exactly: an integer and a pointer read back from the
destination, part of a pointer reads back as poison, and fresh units as
poison. A move whose ranges overlap takes what the source held before it
began, in either direction; a copy whose ranges partly overlap is UB, and
one onto its own range is not. A length of 0 does nothing, whatever the
pointers are (the human's rulings of 2026-11-18 on #234). A poison pointer
with another length is UB, and so is a length past the allocation, at
once, however long. In memory 1, of 16-bit units, the length counts those
units. A poison length chooses its value: over an allocation of one unit,
an `i1` length has two paths and neither is UB. Then the axioms of the
obligations that `memCopy` meets with memory.
-/

namespace FirTest.MemCopy

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

/-- The rule of a copy or a move of the kind `k` in memory `n`, of a length
of `iW`, from `S`. -/
def copy (k : CopyKind) (n w : Nat) (d s : PoisonOr Pointer) (l : PoisonOr (BitVec w))
    (S : Mems) : Except String Mems :=
  after (memCopyRule lay id k w n d s l) S

/-- A store of an `iW` through `p` in memory `n`. -/
def store (n w : Nat) (v : BitVec w) (p : Pointer) (S : Mems) : Except String Mems :=
  after (storeRule lay id w (some 1) n (.value v) (.value p)) S

/-- A store of a pointer of memory 0 through `p` in memory 0. -/
def storeP (q p : Pointer) (S : Mems) : Except String Mems :=
  after (storePtrRule lay id 0 (some 1) 0 (.value q) (.value p)) S

/-- The reason for the UB that a computation ends with, if it does. -/
def ubOf {α : Type} : Except String α → Option String
  | .error r => some r
  | .ok _ => none

/-- What a load of an `iW` through `p` in memory `n` gives from `S`. -/
def load (n w : Nat) (p : Pointer) (S : Mems) : Option (PoisonOr (BitVec w)) :=
  match (loadRule lay id w (some 1) n (.value p) : M _) S with
  | .pure (.cons v .nil, _) => some v
  | _ => none

/-- What a load of a pointer of memory 0 through `p` gives from `S`. -/
def loadP (p : Pointer) (S : Mems) : Option (PoisonOr Pointer) :=
  match (loadPtrRule lay id 0 (some 1) 0 (.value p) : M _) S with
  | .pure (.cons v .nil, _) => some v
  | _ => none

-- An `i32` copied to another place in its allocation reads back there.
#guard (do
  let (p, S) := alloc 8 0
  let S ← store 0 32 0x04030201 p S
  let S ← copy .copy 0 64 (.value (at_ p 4)) (.value p) (.value 4) S
  pure (load 0 32 (at_ p 4) S)).toOption == some (some (.value 0x04030201))

-- A stored pointer, copied whole, reads back as the same pointer, its
-- provenance kept; copied in part, it reads back as poison. A move of it
-- keeps it too.
#guard (do
  let (p, S) := alloc 16 0
  let S ← storeP ⟨some 0, 3⟩ p S
  let S ← copy .copy 0 64 (.value (at_ p 8)) (.value p) (.value 8) S
  pure (loadP (at_ p 8) S)).toOption == some (some (.value ⟨some 0, 3⟩))
#guard (do
  let (p, S) := alloc 16 0
  let S ← storeP ⟨some 0, 3⟩ p S
  let S ← copy .move 0 8 (.value (at_ p 8)) (.value p) (.value 8) S
  pure (loadP (at_ p 8) S)).toOption == some (some (.value ⟨some 0, 3⟩))
#guard (do
  let (p, S) := alloc 16 0
  let S ← storeP ⟨some 0, 3⟩ p S
  let S ← copy .copy 0 64 (.value (at_ p 8)) (.value p) (.value 4) S
  pure (loadP (at_ p 8) S)).toOption == some (some .poison)

-- Fresh units copied read back as poison.
#guard (do
  let (p, S) := alloc 8 0
  let S ← store 0 32 7 (at_ p 4) S
  let S ← copy .copy 0 64 (.value (at_ p 4)) (.value p) (.value 4) S
  pure (load 0 32 (at_ p 4) S)).toOption == some (some .poison)

-- A move whose ranges overlap takes what the source held before it began:
-- the bytes 1, 2, 3, 4 moved up one give 1, 1, 2, 3, and moved down one
-- give 2, 3, 4, 4.
#guard (do
  let (p, S) := alloc 4 0
  let S ← store 0 32 0x04030201 p S
  let S ← copy .move 0 64 (.value (at_ p 1)) (.value p) (.value 3) S
  pure (load 0 32 p S)).toOption == some (some (.value 0x03020101))
#guard (do
  let (p, S) := alloc 4 0
  let S ← store 0 32 0x04030201 p S
  let S ← copy .move 0 64 (.value p) (.value (at_ p 1)) (.value 3) S
  pure (load 0 32 p S)).toOption == some (some (.value 0x04040302))

-- A copy whose ranges partly overlap is UB, in either direction; a copy
-- onto its own range, and one into the units just past its source, are not.
#guard ubOf (copy .copy 0 64 (.value (at_ (alloc 4 0).1 1)) (.value (alloc 4 0).1) (.value 3)
  (alloc 4 0).2) == some "a memcpy whose ranges partly overlap"
#guard ubOf (copy .copy 0 64 (.value (alloc 4 0).1) (.value (at_ (alloc 4 0).1 1)) (.value 3)
  (alloc 4 0).2) == some "a memcpy whose ranges partly overlap"
#guard (copy .copy 0 64 (.value (alloc 4 0).1) (.value (alloc 4 0).1) (.value 4)
  (alloc 4 0).2 |>.toOption.isSome)
#guard (copy .copy 0 64 (.value (at_ (alloc 4 0).1 2)) (.value (alloc 4 0).1) (.value 2)
  (alloc 4 0).2 |>.toOption.isSome)

-- A length of 0 does nothing, through poison pointers, through pointers
-- with no provenance, and into a freed allocation.
#guard (copy .copy 0 64 .poison .poison (.value 0) (alloc 4 0).2 |>.toOption.isSome)
#guard (copy .move 0 8 (.value ⟨none, 0⟩) (.value ⟨none, 5⟩) (.value 0) (alloc 4 0).2
  |>.toOption.isSome)
#guard (copy .copy 0 64 (.value (alloc 4 0).1) (.value (alloc 4 0).1) (.value 0)
  (alloc 4 0).2.exit |>.toOption.isSome)

-- With another length, a poison pointer is UB, and so is a length past the
-- allocation, however long, a pointer with no provenance and a freed
-- allocation.
#guard ubOf (copy .copy 0 64 .poison (.value (alloc 4 0).1) (.value 1) (alloc 4 0).2) ==
  some "a copy or move through a poison pointer"
#guard ubOf (copy .move 0 64 (.value (alloc 4 0).1) .poison (.value 1) (alloc 4 0).2) ==
  some "a copy or move through a poison pointer"
#guard ubOf (copy .move 0 64 (.value (at_ (alloc 8 0).1 4)) (.value (alloc 8 0).1)
  (.value (2 ^ 63)) (alloc 8 0).2) == some "an access out of bounds"
#guard ubOf (copy .move 0 64 (.value (alloc 4 0).1) (.value ⟨none, 0⟩) (.value 1)
  (alloc 4 0).2) == some "an access through a pointer without provenance"
#guard ubOf (copy .move 0 64 (.value (alloc 4 0).1) (.value (alloc 4 0).1) (.value 1)
  (alloc 4 0).2.exit) == some "an access to a freed allocation"
-- Two pointers with no provenance lie in no allocation, so a copy through
-- them faults for that, not for an overlap.
#guard ubOf (copy .copy 0 64 (.value ⟨none, 0⟩) (.value ⟨none, 2⟩) (.value 4)
  (alloc 4 0).2) == some "an access through a pointer without provenance"

-- In memory 1, of 16-bit units, an `i32` takes two units, and a length of
-- 2 copies it.
#guard (do
  let (p, S) := alloc 4 1
  let S ← store 1 32 0x04030201 p S
  let S ← copy .copy 1 32 (.value (at_ p 2)) (.value p) (.value 2) S
  pure (load 1 32 (at_ p 2) S)).toOption == some (some (.value 0x04030201))
#guard (do
  let (p, S) := alloc 4 1
  let S ← store 1 32 0x04030201 p S
  let S ← copy .copy 1 32 (.value (at_ p 2)) (.value p) (.value 1) S
  pure (load 1 16 (at_ p 3) S)).toOption == some (some .poison)

-- A poison `i1` length over an allocation of one unit chooses 0 or 1, and
-- neither path is UB.
#guard match (memCopyRule lay id .move 1 0 (.value (alloc 1 0).1) (.value (alloc 1 0).1)
    .poison : M _) (alloc 1 0).2 with
  | .choose 1 .bits k => (k 0 matches .pure _) && (k 1 matches .pure _)
  | _ => false
-- A poison length is UB where some length is.
#guard match (memCopyRule lay id .copy 1 0 (.value (alloc 1 0).1) (.value ⟨none, 0⟩)
    .poison : M _) (alloc 1 0).2 with
  | .choose 1 .bits k => (k 0 matches .pure _) && (k 1 matches .ub _)
  | _ => false

/-! # Axioms -/

/-- info: 'Fir.Core.memCopy_memTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.memCopy_memTotal

/-- info: 'Fir.Core.memCopy_memMonotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.memCopy_memMonotone

/-- info: 'Fir.Core.memCopy_readsNot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.memCopy_readsNot

/-- info: 'Fir.Core.memCopy_writesNot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.memCopy_writesNot

/-- info: 'Fir.Core.memCopy_allocatesNot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.memCopy_allocatesNot

/-- info: 'Fir.Core.memCopy_finitelyMany' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.memCopy_finitelyMany

/-- info: 'Fir.Core.memCopy_memPropagates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.memCopy_memPropagates

/-- info: 'Fir.Core.memCopy_memReturnsOnDefined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.memCopy_memReturnsOnDefined

/-- info: 'Fir.Core.memCopy_makesNoPoison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.memCopy_makesNoPoison

end FirTest.MemCopy
