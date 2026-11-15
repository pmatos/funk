import Fir

/-!
Tests of `load`'s rule with memory, run in the state layer over the tree of
choices, the monad that `fir-ref run` computes in. No op stores yet, so a
test writes units with the memory model's own store, then runs the rule:
fresh memory reads poison; units of bits decode in the memory's byte order,
with the bits past the type's width ignored (an `i1` from `0xFF` is 1); a
pointer's fragments decode to poison; and a poison pointer, an access out
of bounds, to a freed allocation, through a pointer with no provenance, or
misaligned at some address its block may get, is UB (the human's rulings
of 2026-11-11 on #231 and of 2026-11-14 on #388). Memory 1 has 16-bit
units, so an `i32` takes two of them there. Then the axioms of the
obligations that `load` meets with memory, and of the rejection of a load
declared without a read.
-/

namespace FirTest.Load

open Fir Fir.Core Fir.Memory

/-- Memory 1 has 16-bit units and 32-bit pointers; every other memory has
the default entry: 8-bit units and 64-bit pointers. -/
def lay : Nat → MemLayout := fun n =>
  if n = 1 then { mem := 1, unit := 16, pointer := 32, order := .little } else MemLayout.default

abbrev Mems := Memories Nat (unitsOf lay)

abbrev M := StateT Mems (ChoiceTree Op)

/-- What a load ends with on its one path: a value, or the reason for its
UB. -/
inductive Out (w : Nat) where
  | ok (v : PoisonOr (BitVec w))
  | error (reason : String)
  deriving DecidableEq

/-- What `c` ends with from `S` on its one path. -/
def outcome (c : M (HVector toType [Ty.int w])) (S : Mems) : Out w :=
  match c S with
  | .pure (.cons v .nil, _) => .ok v
  | .ub r => .error r
  | _ => .error "no single outcome"

/-- `load` of an `iW` with the alignment `a` through `p`, in memory `n`,
from the memories `S`. -/
def load (w : Nat) (a : Option Nat) (n : Nat) (p : PoisonOr Pointer) (S : Mems) : Out w :=
  outcome (loadRule lay id w a n p) S

/-- Inside a call, an allocation of `c` values of `iW` in memory `n`,
aligned to `a`: its pointer and the memories after it. -/
def alloc (w c : Nat) (a : Option Nat) (n : Nat) : Pointer × Mems :=
  Memories.empty.enter.alloc n .stack (allocaShape lay id (.int w) c a n).1
    (allocaShape lay id (.int w) c a n).2

/-- The memories after storing the bytes `bs` at the start of an allocation
of `c` values of `iW` in memory 0, aligned to `a`, and its pointer. -/
def stored (w c : Nat) (a : Option Nat) (bs : List (MemUnit 8)) : Option (Pointer × Mems) :=
  let (p, S) := alloc w c a 0
  match S.store 0 p bs 1 with
  | .ok S' => some (p, S')
  | .error _ => none

-- Fresh memory reads poison.
#guard load 32 none 0 (.value (alloc 32 1 none 0).1) (alloc 32 1 none 0).2 == .ok .poison

-- Bytes decode least significant first, the order of memory 0.
#guard ((stored 32 1 none [.bits 1, .bits 2, .bits 3, .bits 4]).map fun (p, S) =>
    load 32 none 0 (.value p) S) == some (.ok (.value 0x04030201))

-- An odd width takes whole units, and a load ignores the bits past its
-- width: an `i1` from `0xFF` is 1, and an `i20` from three `0xFF` is all
-- ones.
#guard ((stored 1 1 none [.bits 0xFF]).map fun (p, S) => load 1 none 0 (.value p) S) ==
  some (.ok (.value 1))
#guard ((stored 20 1 none [.bits 0xFF, .bits 0xFF, .bits 0xFF]).map fun (p, S) =>
    load 20 none 0 (.value p) S) == some (.ok (.value 0xFFFFF))

-- A poison unit among the units gives poison.
#guard ((stored 16 1 none [.bits 1]).map fun (p, S) => load 16 none 0 (.value p) S) ==
  some (.ok .poison)

-- A punned load of a pointer's fragments gives poison.
#guard ((stored 64 1 none (encodePtr 0 8 .little (.value ⟨some 0, 0⟩))).map fun (p, S) =>
    load 64 none 0 (.value p) S) == some (.ok .poison)

-- A poison pointer is UB.
#guard load 32 none 0 .poison (alloc 32 1 none 0).2 == .error "a load through a poison pointer"

-- A pointer with no provenance, out of bounds, past the end, and a freed
-- allocation are UB.
#guard load 32 none 0 (.value ⟨none, 0⟩) (alloc 32 1 none 0).2 ==
  .error "an access through a pointer without provenance"
#guard load 64 none 0 (.value (alloc 32 1 none 0).1) (alloc 32 1 none 0).2 ==
  .error "an access out of bounds"
#guard load 8 none 0 (.value ⟨some 0, 4⟩) (alloc 32 1 none 0).2 == .error "an access out of bounds"
#guard load 8 none 0 (.value ⟨some 0, -1⟩) (alloc 32 1 none 0).2 == .error "an access out of bounds"
#guard load 32 none 0 (.value (alloc 32 1 none 0).1) (alloc 32 1 none 0).2.exit ==
  .error "an access to a freed allocation"

-- An `i32` at its natural alignment, 4, from 16 bytes aligned to 1 is
-- misaligned, even at offset 0; aligned to 4 it reads poison. Promising
-- only 1 makes it aligned. At offset 2 of a block aligned to 4, an access
-- aligned to 4 is misaligned, and one aligned to 2 is not.
#guard load 32 none 0 (.value (alloc 8 16 none 0).1) (alloc 8 16 none 0).2 ==
  .error "a misaligned access"
#guard load 32 none 0 (.value (alloc 8 16 (some 4) 0).1) (alloc 8 16 (some 4) 0).2 == .ok .poison
#guard load 32 (some 1) 0 (.value (alloc 8 16 none 0).1) (alloc 8 16 none 0).2 == .ok .poison
#guard load 32 none 0 (.value ⟨some 0, 2⟩) (alloc 8 16 (some 4) 0).2 == .error "a misaligned access"
#guard load 32 (some 2) 0 (.value ⟨some 0, 2⟩) (alloc 8 16 (some 4) 0).2 == .ok .poison

-- A fault comes before a misaligned access: an access out of bounds is
-- out of bounds, whatever its alignment.
#guard load 64 (some 8) 0 (.value (alloc 8 4 none 0).1) (alloc 8 4 none 0).2 ==
  .error "an access out of bounds"

-- In memory 1, of 16-bit units, an `i32` takes 2 units and is aligned to 2.
#guard load 32 none 1 (.value (alloc 32 1 none 1).1) (alloc 32 1 none 1).2 == .ok .poison
#guard load 32 none 1 (.value ⟨some 0, 1⟩) (alloc 32 2 none 1).2 == .error "a misaligned access"
#guard load 32 none 0 (.value (alloc 32 1 none 1).1) (alloc 32 1 none 1).2 ==
  .error "an access through a pointer without provenance"

/-! # Axioms -/

/-- info: 'Fir.Core.load_memTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.load_memTotal

/-- info: 'Fir.Core.load_memMonotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.load_memMonotone

/-- info: 'Fir.Core.load_readsNot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.load_readsNot

/-- info: 'Fir.Core.load_memReturnsOnDefined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.load_memReturnsOnDefined

/-- info: 'Fir.Core.Unlawful.loadNoRead_unlawful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.Unlawful.loadNoRead_unlawful

end FirTest.Load
