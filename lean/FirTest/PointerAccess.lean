import Fir

/-!
Tests of the rules of `alloca` of pointers, `loadPtr` and `storePtr` with
memory, run in the state layer over the tree of choices, the monad that
`fir-ref run` computes in. A pointer stored and loaded back is the same
pointer, provenance and offset included, in memory 0 and in a memory of
16-bit units with 32-bit pointers, where a pointer of memory 0 takes four
units and one of memory 1 two. A pointer load gives poison from fresh
memory, from units of bits, from a pointer of another memory and from a
pointer partly overwritten, and an integer load from a pointer's fragments
gives poison (the human's rulings of 2026-11-11 on #231, Q3). The default
alignment of `ptr<M>` in memory `N` is its natural one there, and in memory
`M` itself the alignment that `M`'s entry gives its pointers. A poison
pointer, an access out of bounds, to a freed allocation, through a pointer
with no provenance, or misaligned is UB. Then the axioms of the
obligations that `loadPtr` and `storePtr` meet with memory.
-/

namespace FirTest.PointerAccess

open Fir Fir.Core Fir.Memory

/-- Memory 1 has 16-bit units and 32-bit pointers, aligned to 4 units;
every other memory has the default entry: 8-bit units and 64-bit
pointers. -/
def lay : Nat → MemLayout := fun n =>
  if n = 1 then { mem := 1, unit := 16, pointer := 32, order := .little, align := some 4 }
  else MemLayout.default

abbrev Mems := Memories Nat (unitsOf lay)

abbrev M := StateT Mems (ChoiceTree Op)

/-- What an access ends with on its one path: a value, or the reason for
its UB. -/
inductive Out (α : Type) where
  | ok (v : α)
  | error (reason : String)
  deriving DecidableEq

/-- Inside a call, an allocation of `c` values of `t` in memory `n`,
aligned to `a`: its pointer and the memories after it. -/
def alloc (t : Ty) (c : Nat) (a : Option Nat) (n : Nat) : Pointer × Mems :=
  Memories.empty.enter.alloc n .stack (allocaShape lay id t c a n).1 (allocaShape lay id t c a n).2

/-- What `c`, ending in a pointer load, ends with from `S` on its one
path. -/
def outcome {mq : Nat} (c : M (HVector toType [Ty.ptr mq])) (S : Mems) : Out (PoisonOr Pointer) :=
  match c S with
  | .pure (.cons v .nil, _) => .ok v
  | .ub r => .error r
  | _ => .error "no single outcome"

/-- What `c`, ending in an integer load, ends with from `S` on its one
path. -/
def outcomeInt {w : Nat} (c : M (HVector toType [Ty.int w])) (S : Mems) :
    Out (PoisonOr (BitVec w)) :=
  match c S with
  | .pure (.cons v .nil, _) => .ok v
  | .ub r => .error r
  | _ => .error "no single outcome"

/-- In memory `n`, from `S`: a `storePtr` of `v`, a pointer of memory `mp`,
through `p`, then a `loadPtr` of a pointer of memory `mq` through `q`. -/
def storeLoad (n : Nat) (S : Mems) (mp : Nat) (v : PoisonOr Pointer) (p : PoisonOr Pointer)
    (mq : Nat) (q : PoisonOr Pointer) : Out (PoisonOr Pointer) :=
  outcome (do
    let _ ← (storePtrRule lay id mp none n v p : M _)
    loadPtrRule lay id mq none n q) S

/-- A pointer of memory `mp` stored through the pointer of a fresh
allocation of one `ptr<mp>` in memory `n`, then loaded back. -/
def roundTrip (n mp : Nat) (v : PoisonOr Pointer) : Out (PoisonOr Pointer) :=
  let (p, S) := alloc (.ptr mp) 1 none n
  storeLoad n S mp v (.value p) mp (.value p)

/-- The pointer of an allocation, moved by `o` units. -/
def at_ (p : Pointer) (o : Int) : Pointer := ⟨p.prov, p.offset + o⟩

/-- An allocation of `ptr<M>` takes the units of `M`'s pointers in memory
`N`, at the default alignment of `ptr<M>` there. -/
example : allocaShape lay id (.ptr 0) 2 none 0 = (16, 8) ∧
    allocaShape lay id (.ptr 1) 1 none 1 = (2, 4) ∧
    allocaShape lay id (.ptr 0) 1 none 1 = (4, 4) ∧
    allocaShape lay id (.ptr 1) 1 none 0 = (4, 4) ∧
    allocaShape lay id (.ptr 1) 3 (some 2) 1 = (6, 2) := by
  decide +kernel

-- A pointer stored and loaded back is the same pointer, its provenance and
-- offset kept, in either memory, of either memory; poison is poison.
#guard roundTrip 0 0 (.value ⟨some 7, 3⟩) == .ok (.value ⟨some 7, 3⟩)
#guard roundTrip 0 0 (.value ⟨none, -5⟩) == .ok (.value ⟨none, -5⟩)
#guard roundTrip 0 1 (.value ⟨some 2, 0⟩) == .ok (.value ⟨some 2, 0⟩)
#guard roundTrip 1 1 (.value ⟨some 2, 9⟩) == .ok (.value ⟨some 2, 9⟩)
#guard roundTrip 1 0 (.value ⟨some 0, 1⟩) == .ok (.value ⟨some 0, 1⟩)
#guard roundTrip 0 0 .poison == .ok .poison
#guard roundTrip 1 1 .poison == .ok .poison

-- A pointer load from fresh memory is poison.
#guard (let (p, S) := alloc (.ptr 0) 1 none 0
  outcome (loadPtrRule lay id 0 none 0 (.value p) : M _) S) == .ok .poison

-- A pointer of memory 1 does not load as a pointer of memory 0, which takes
-- other units, nor the other way round: each gives poison.
#guard (let (p, S) := alloc (.ptr 0) 1 none 0
  storeLoad 0 S 1 (.value ⟨some 3, 0⟩) (.value p) 0 (.value p)) == .ok .poison
#guard (let (p, S) := alloc (.ptr 0) 1 none 1
  storeLoad 1 S 0 (.value ⟨some 3, 0⟩) (.value p) 1 (.value p)) == .ok .poison

-- A pointer load from units of bits is poison, and so is an integer load
-- from a pointer's fragments, whole or in part.
#guard (let (p, S) := alloc (.ptr 0) 1 none 0
  outcome (do
    let _ ← (storeRule lay id 64 none 0 (.value 0x1234) (.value p) : M _)
    loadPtrRule lay id 0 none 0 (.value p)) S) == .ok .poison
#guard (let (p, S) := alloc (.ptr 0) 1 none 0
  outcomeInt (do
    let _ ← (storePtrRule lay id 0 none 0 (.value ⟨some 0, 0⟩) (.value p) : M _)
    loadRule lay id 64 none 0 (.value p)) S) == .ok .poison
#guard (let (p, S) := alloc (.ptr 0) 1 none 0
  outcomeInt (do
    let _ ← (storePtrRule lay id 0 none 0 (.value ⟨some 0, 0⟩) (.value p) : M _)
    loadRule lay id 8 none 0 (.value (at_ p 3))) S) == .ok .poison

-- A pointer with one byte overwritten is no longer a pointer.
#guard (let (p, S) := alloc (.ptr 0) 1 none 0
  outcome (do
    let _ ← (storePtrRule lay id 0 none 0 (.value ⟨some 0, 0⟩) (.value p) : M _)
    let _ ← (storeRule lay id 8 none 0 (.value 0) (.value (at_ p 7)) : M _)
    loadPtrRule lay id 0 none 0 (.value p)) S) == .ok .poison

-- A pointer copied unit by unit, as integers of one unit, keeps nothing:
-- the copy holds no fragments. Copied as a pointer, it keeps its provenance.
#guard (let (p, S) := alloc (.ptr 0) 2 none 0
  outcome (do
    let _ ← (storePtrRule lay id 0 none 0 (.value ⟨some 0, 5⟩) (.value p) : M _)
    let r ← (loadPtrRule lay id 0 none 0 (.value p) : M _)
    match r with
    | .cons v .nil =>
      let _ ← (storePtrRule lay id 0 none 0 v (.value (at_ p 8)) : M _)
      loadPtrRule lay id 0 none 0 (.value (at_ p 8))) S) == .ok (.value ⟨some 0, 5⟩)

-- The default alignment of a pointer of memory 1 in memory 1 is the 4 units
-- its entry gives, so an access at offset 2 of a block aligned to 4 is
-- misaligned; a pointer of memory 0 in memory 1 is aligned to 4 too, its
-- natural alignment there, and one of memory 1 in memory 0 to 4 bytes.
#guard (let (p, S) := alloc (.ptr 1) 4 none 1
  outcome (loadPtrRule lay id 1 none 1 (.value (at_ p 2)) : M _) S) ==
    .error "a misaligned access"
#guard (let (p, S) := alloc (.ptr 1) 4 none 1
  outcome (loadPtrRule lay id 1 (some 2) 1 (.value (at_ p 2)) : M _) S) ==
    .ok .poison
#guard (let (p, S) := alloc (.ptr 0) 2 none 1
  outcome (loadPtrRule lay id 0 none 1 (.value (at_ p 2)) : M _) S) ==
    .error "a misaligned access"
#guard (let (p, S) := alloc (.int 8) 8 none 0
  outcome (loadPtrRule lay id 1 none 0 (.value p) : M _) S) ==
    .error "a misaligned access"

-- A poison pointer, no provenance, out of bounds, a freed allocation are
-- UB; a store of a poison pointer through a defined one is not.
#guard (let (_, S) := alloc (.ptr 0) 1 none 0
  outcome (loadPtrRule lay id 0 none 0 .poison : M _) S) ==
    .error "a load through a poison pointer"
#guard (let (_, S) := alloc (.ptr 0) 1 none 0
  storeLoad 0 S 0 (.value ⟨none, 0⟩) .poison 0 .poison) == .error "a store through a poison pointer"
#guard (let (_, S) := alloc (.ptr 0) 1 none 0
  outcome (loadPtrRule lay id 0 none 0 (.value ⟨none, 0⟩) : M _) S) ==
    .error "an access through a pointer without provenance"
#guard (let (p, S) := alloc (.ptr 0) 1 none 0
  storeLoad 0 S 0 (.value p) (.value (at_ p 8)) 0 (.value p)) == .error "an access out of bounds"
#guard (let (p, S) := alloc (.ptr 0) 1 none 0
  outcome (loadPtrRule lay id 0 none 0 (.value p) : M _) S.exit) ==
    .error "an access to a freed allocation"
#guard (let (p, S) := alloc (.ptr 0) 1 none 0
  storeLoad 0 S 0 .poison (.value p) 0 (.value p)) == .ok .poison

/-! # Axioms -/

/-- info: 'Fir.Core.loadPtr_memTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.loadPtr_memTotal

/-- info: 'Fir.Core.loadPtr_memMonotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.loadPtr_memMonotone

/-- info: 'Fir.Core.loadPtr_readsNot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.loadPtr_readsNot

/-- info: 'Fir.Core.loadPtr_memPropagates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.loadPtr_memPropagates

/-- info: 'Fir.Core.loadPtr_memReturnsOnDefined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.loadPtr_memReturnsOnDefined

/-- info: 'Fir.Core.loadPtr_finitelyMany' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.loadPtr_finitelyMany

/-- info: 'Fir.Core.storePtr_memTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.storePtr_memTotal

/-- info: 'Fir.Core.storePtr_memMonotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.storePtr_memMonotone

/-- info: 'Fir.Core.storePtr_readsNot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.storePtr_readsNot

/-- info: 'Fir.Core.storePtr_memPropagates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.storePtr_memPropagates

/-- info: 'Fir.Core.storePtr_memReturnsOnDefined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.storePtr_memReturnsOnDefined

/-- info: 'Fir.Core.storePtr_finitelyMany' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.storePtr_finitelyMany

/-- info: 'Fir.Core.storePtr_makesNoPoison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.storePtr_makesNoPoison

end FirTest.PointerAccess
