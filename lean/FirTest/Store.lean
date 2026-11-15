import Fir

/-!
Tests of `store`'s rule with memory, run in the state layer over the tree
of choices, the monad that `fir-ref run` computes in. A store, then a load
of what it stored, gives the value back, at every width, odd ones included,
and in a memory of 16-bit units, where an `i32` takes two units. A store
writes the encoding of its value: the units of an odd width are padded with
zeros, so a wider load of them sees zero bits there; a narrower load gives
the low units, in the memory's byte order; a wider load past what was
stored reads the poison of fresh memory; and a store of poison makes its
units poison. A poison pointer, an access out of bounds, to a freed
allocation, through a pointer with no provenance, or misaligned at some
address its block may get, is UB (the human's rulings of 2026-11-11 on #231
and of 2026-11-14 on #388). Then the axioms of the obligations that `store`
meets with memory, and of the rejection of a store declared without a
write.
-/

namespace FirTest.Store

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

/-- Inside a call, an allocation of `c` values of `iW` in memory `n`,
aligned to `a`: its pointer and the memories after it. -/
def alloc (w c : Nat) (a : Option Nat) (n : Nat) : Pointer × Mems :=
  Memories.empty.enter.alloc n .stack (allocaShape lay id (.int w) c a n).1
    (allocaShape lay id (.int w) c a n).2

/-- What `c`, a store and then a load of an `iW`, ends with from `S` on its
one path. -/
def outcome (c : M (HVector toType [Ty.int w])) (S : Mems) : Out w :=
  match c S with
  | .pure (.cons v .nil, _) => .ok v
  | .ub r => .error r
  | _ => .error "no single outcome"

/-- In memory `n`, from the memories `S`: a `store` of `v`, an `iW`, aligned
to `a` through `p`, then a `load` of an `iV`, `V = w'`, aligned to `b`
through `q`. -/
def storeLoad (n : Nat) (S : Mems) (w : Nat) (v : PoisonOr (BitVec w)) (a : Option Nat)
    (p : PoisonOr Pointer) (w' : Nat) (b : Option Nat) (q : PoisonOr Pointer) : Out w' :=
  outcome (do
    let _ ← (storeRule lay id w a n v p : M _)
    loadRule lay id w' b n q) S

/-- A store of `v`, an `iW`, through the pointer of a fresh allocation of
one `iW` in memory `n`, then a load of it back. -/
def roundTrip (n w : Nat) (v : PoisonOr (BitVec w)) : Out w :=
  let (p, S) := alloc w 1 none n
  storeLoad n S w v none (.value p) w none (.value p)

/-- The reason a store of `v`, an `iW`, aligned to `a` through `p` in
memory `n` is UB from `S`, or none when it ends. -/
def storeUB (n : Nat) (S : Mems) (w : Nat) (v : PoisonOr (BitVec w)) (a : Option Nat)
    (p : PoisonOr Pointer) : Option String :=
  match (storeRule lay id w a n v p : M _) S with
  | .pure _ => none
  | .ub r => some r
  | _ => some "no single outcome"

-- A store then a load gives the value back, at every width of the
-- interpreter's side, the odd ones included.
#guard roundTrip 0 1 (.value 1) == .ok (.value 1)
#guard roundTrip 0 7 (.value 0x55) == .ok (.value 0x55)
#guard roundTrip 0 8 (.value 0xAB) == .ok (.value 0xAB)
#guard roundTrip 0 16 (.value 0xBEEF) == .ok (.value 0xBEEF)
#guard roundTrip 0 32 (.value 0x04030201) == .ok (.value 0x04030201)
#guard roundTrip 0 33 (.value 0x1FFFFFFFF) == .ok (.value 0x1FFFFFFFF)
#guard roundTrip 0 64 (.value 0x0123456789ABCDEF) == .ok (.value 0x0123456789ABCDEF)
#guard roundTrip 0 128 (.value (BitVec.allOnes 128)) == .ok (.value (BitVec.allOnes 128))

-- In memory 1, of 16-bit units, an `i32` takes two units, an `i8` one, and
-- each reads back.
#guard roundTrip 1 32 (.value 0x04030201) == .ok (.value 0x04030201)
#guard roundTrip 1 8 (.value 0xAB) == .ok (.value 0xAB)
#guard roundTrip 1 20 (.value 0xFFFFF) == .ok (.value 0xFFFFF)

-- A store of poison makes its units poison.
#guard roundTrip 0 32 .poison == .ok .poison
#guard roundTrip 1 32 .poison == .ok .poison

-- Bytes are stored least significant first, the order of memory 0: a
-- narrower load gives the low byte or bytes, and a byte at offset 1 is the
-- second; in memory 1, an `i16` load gives the low unit.
#guard (let (p, S) := alloc 32 1 none 0
  storeLoad 0 S 32 (.value 0x04030201) none (.value p) 16 none (.value p)) == .ok (.value 0x0201)
#guard (let (p, S) := alloc 32 1 none 0
  storeLoad 0 S 32 (.value 0x04030201) none (.value p) 8 none (.value ⟨p.prov, 1⟩)) ==
    .ok (.value 0x02)
#guard (let (p, S) := alloc 32 1 none 1
  storeLoad 1 S 32 (.value 0x04030201) none (.value p) 16 none (.value p)) == .ok (.value 0x0201)

-- An odd width is stored in whole units with zero padding: an `i1` of 1
-- stored and loaded as an `i8` is 1, and an `i20` of all ones loaded as an
-- `i24` has zeros above its 20 bits.
#guard (let (p, S) := alloc 8 1 none 0
  storeLoad 0 S 1 (.value 1) none (.value p) 8 none (.value p)) == .ok (.value 1)
#guard (let (p, S) := alloc 32 1 none 0
  storeLoad 0 S 20 (.value 0xFFFFF) none (.value p) 24 none (.value p)) == .ok (.value 0x0FFFFF)

-- A wider load past what was stored reads fresh memory, so it is poison;
-- past the allocation it is out of bounds.
#guard (let (p, S) := alloc 32 2 none 0
  storeLoad 0 S 32 (.value 7) none (.value p) 64 (some 4) (.value p)) == .ok .poison
#guard (let (p, S) := alloc 32 1 none 0
  storeLoad 0 S 32 (.value 7) none (.value p) 64 (some 4) (.value p)) ==
    .error "an access out of bounds"

-- A store replaces only its own units: a byte stored at offset 1 of an
-- `i32` changes that byte.
#guard (let (p, S) := alloc 32 1 none 0
  match (storeRule lay id 32 none 0 (.value 0x04030201) (.value p) : M _) S with
  | .pure (_, S') => storeLoad 0 S' 8 (.value 9) none (.value ⟨p.prov, 1⟩) 32 none (.value p)
  | _ => .error "no single outcome") == .ok (.value 0x04030901)

-- A poison pointer, no provenance, out of bounds at either end, a freed
-- allocation and a misaligned access are UB; a fault comes before a
-- misaligned access.
#guard storeUB 0 (alloc 32 1 none 0).2 32 (.value 0) none .poison ==
  some "a store through a poison pointer"
#guard storeUB 0 (alloc 32 1 none 0).2 32 .poison none .poison ==
  some "a store through a poison pointer"
#guard storeUB 0 (alloc 32 1 none 0).2 32 (.value 0) none (.value ⟨none, 0⟩) ==
  some "an access through a pointer without provenance"
#guard storeUB 0 (alloc 32 1 none 0).2 64 (.value 0) (some 4) (.value (alloc 32 1 none 0).1) ==
  some "an access out of bounds"
#guard storeUB 0 (alloc 32 1 none 0).2 8 (.value 0) none (.value ⟨some 0, 4⟩) ==
  some "an access out of bounds"
#guard storeUB 0 (alloc 32 1 none 0).2 8 (.value 0) none (.value ⟨some 0, -1⟩) ==
  some "an access out of bounds"
#guard storeUB 0 (alloc 32 1 none 0).2.exit 32 (.value 0) none (.value (alloc 32 1 none 0).1) ==
  some "an access to a freed allocation"
#guard storeUB 0 (alloc 8 16 none 0).2 32 (.value 0) none (.value (alloc 8 16 none 0).1) ==
  some "a misaligned access"
#guard storeUB 0 (alloc 8 16 (some 4) 0).2 32 (.value 0) none (.value ⟨some 0, 2⟩) ==
  some "a misaligned access"
#guard storeUB 0 (alloc 8 16 (some 4) 0).2 32 (.value 0) (some 2) (.value ⟨some 0, 2⟩) == none
#guard storeUB 0 (alloc 8 16 none 0).2 32 (.value 0) (some 1) (.value (alloc 8 16 none 0).1) == none
#guard storeUB 0 (alloc 8 4 none 0).2 64 (.value 0) (some 8) (.value (alloc 8 4 none 0).1) ==
  some "an access out of bounds"
#guard storeUB 1 (alloc 32 2 none 1).2 32 (.value 0) none (.value ⟨some 0, 1⟩) ==
  some "a misaligned access"

-- A store of poison through a defined pointer is not UB; it faults only
-- where a store of a defined value would.
#guard storeUB 0 (alloc 32 1 none 0).2 32 .poison none (.value (alloc 32 1 none 0).1) == none
#guard storeUB 0 (alloc 32 1 none 0).2 64 .poison (some 4) (.value (alloc 32 1 none 0).1) ==
  some "an access out of bounds"

/-! # Axioms -/

/-- info: 'Fir.Core.store_memTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.store_memTotal

/-- info: 'Fir.Core.store_memMonotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.store_memMonotone

/-- info: 'Fir.Core.store_readsNot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.store_readsNot

/-- info: 'Fir.Core.store_memPropagates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.store_memPropagates

/-- info: 'Fir.Core.store_memReturnsOnDefined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.store_memReturnsOnDefined

/-- info: 'Fir.Core.Unlawful.storeNoWrite_unlawful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.Unlawful.storeNoWrite_unlawful

end FirTest.Store
