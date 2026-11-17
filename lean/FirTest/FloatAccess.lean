import Fir

/-!
Tests of the rules of `alloca` of floats, `loadFloat` and `storeFloat` with
memory, run in the state layer over the tree of choices, the monad that
`fir-ref run` computes in (#264). A float stored and loaded back is the
same float, a NaN's payload and sign included, at every aliased format and
at `float<2,1>`, whose 4 bits take one byte with the top 4 bits zero. A
float stored and loaded as the integer of its width gives its bits, and an
integer stored and loaded as a float of its width gives the float with its
bits. A float load gives poison from fresh memory and from a pointer's
fragments. The default alignment of a float is the natural alignment of its
size, and a memory of 16-bit units holds an `f32` in two units. A poison
pointer, an access out of bounds or misaligned is UB. Then the axioms of
the obligations that `loadFloat` and `storeFloat` meet with memory.
-/

namespace FirTest.FloatAccess

open Fir Fir.Core Fir.Memory

/-- Memory 1 has 16-bit units and 32-bit pointers; every other memory has
the default entry: 8-bit units and 64-bit pointers. -/
def lay : Nat → MemLayout := fun n =>
  if n = 1 then { mem := 1, unit := 16, pointer := 32, order := .little, align := none }
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

/-- What `c`, ending in a float load, ends with from `S` on its one path. -/
def outcome {e m : Nat} (c : M (HVector toType [Ty.float e m])) (S : Mems) :
    Out (PoisonOr (BitVec (floatWidth e m))) :=
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

/-- A float of `float<e,m>` stored through the pointer of a fresh
allocation of one in memory `n`, then loaded back. -/
def roundTrip (n e m : Nat) (v : PoisonOr (BitVec (floatWidth e m))) :
    Out (PoisonOr (BitVec (floatWidth e m))) :=
  let (p, S) := alloc (.float e m) 1 none n
  outcome (do
    let _ ← (storeFloatRule lay id e m none n v (.value p) : M _)
    loadFloatRule lay id e m none n (.value p)) S

/-- A float of `float<e,m>` stored, then loaded as the integer of its
width, in memory `n`. -/
def asBits (n e m : Nat) (v : PoisonOr (BitVec (floatWidth e m))) :
    Out (PoisonOr (BitVec (floatWidth e m))) :=
  let (p, S) := alloc (.float e m) 1 none n
  outcomeInt (do
    let _ ← (storeFloatRule lay id e m none n v (.value p) : M _)
    loadRule lay id (floatWidth e m) none n (.value p)) S

/-- An integer of the width of `float<e,m>` stored, then loaded as that
float, in memory `n`. -/
def ofBits (n e m : Nat) (v : PoisonOr (BitVec (floatWidth e m))) :
    Out (PoisonOr (BitVec (floatWidth e m))) :=
  let (p, S) := alloc (.int (floatWidth e m)) 1 none n
  outcome (do
    let _ ← (storeRule lay id (floatWidth e m) none n v (.value p) : M _)
    loadFloatRule lay id e m none n (.value p)) S

/-- The pointer of an allocation, moved by `o` units. -/
def at_ (p : Pointer) (o : Int) : Pointer := ⟨p.prov, p.offset + o⟩

/-- A float takes the units of its bits at the natural alignment of its
size: in memory 0, two bytes aligned to 2 for `f16` and `bf16`, four for
`f32`, eight for `f64`, sixteen for `f128`, and one byte for `float<2,1>`;
in memory 1, of 16-bit units, an `f32` takes two units aligned to 2. -/
example : allocaShape lay id (.float 5 10) 1 none 0 = (2, 2) ∧
    allocaShape lay id (.float 8 7) 1 none 0 = (2, 2) ∧
    allocaShape lay id (.float 8 23) 1 none 0 = (4, 4) ∧
    allocaShape lay id (.float 11 52) 3 none 0 = (24, 8) ∧
    allocaShape lay id (.float 15 112) 1 none 0 = (16, 16) ∧
    allocaShape lay id (.float 2 1) 5 none 0 = (5, 1) ∧
    allocaShape lay id (.float 8 23) 1 none 1 = (2, 2) ∧
    allocaShape lay id (.float 8 23) 1 (some 8) 0 = (4, 8) := by
  decide +kernel

-- A float stored and loaded back is the same float at every aliased format,
-- a NaN's payload and sign kept, and poison is poison.
#guard roundTrip 0 8 23 (.value 0x3f800000) == .ok (.value 0x3f800000)
#guard roundTrip 0 8 23 (.value 0xffc00123) == .ok (.value 0xffc00123)
#guard roundTrip 0 8 23 (.value 0x7f800001) == .ok (.value 0x7f800001)
#guard roundTrip 0 11 52 (.value 0x7ff0000000000001) == .ok (.value 0x7ff0000000000001)
#guard roundTrip 0 11 52 (.value 0x8000000000000000) == .ok (.value 0x8000000000000000)
#guard roundTrip 0 5 10 (.value 0xfe01) == .ok (.value 0xfe01)
#guard roundTrip 0 8 7 (.value 0x7fc1) == .ok (.value 0x7fc1)
#guard roundTrip 0 15 112 (.value 0x7fff8000000000000000000000000001) ==
  .ok (.value 0x7fff8000000000000000000000000001)
#guard roundTrip 0 2 1 (.value 0xf) == .ok (.value 0xf)
#guard roundTrip 0 8 23 .poison == .ok .poison
#guard roundTrip 1 8 23 (.value 0xff800000) == .ok (.value 0xff800000)
#guard roundTrip 1 11 52 (.value 0x7ff8000000000000) == .ok (.value 0x7ff8000000000000)

-- A float loaded as the integer of its width gives its bits, and an
-- integer loaded as a float of its width gives the float with its bits.
#guard asBits 0 8 23 (.value 0x7fc00001) == .ok (.value 0x7fc00001)
#guard asBits 0 11 52 (.value 0xfff0000000000000) == .ok (.value 0xfff0000000000000)
#guard asBits 0 2 1 (.value 0x9) == .ok (.value 0x9)
#guard asBits 1 5 10 (.value 0x7c01) == .ok (.value 0x7c01)
#guard asBits 0 8 23 .poison == .ok .poison
#guard ofBits 0 8 23 (.value 0xff800001) == .ok (.value 0xff800001)
#guard ofBits 0 15 112 (.value 1) == .ok (.value 1)
#guard ofBits 1 8 7 (.value 0x8000) == .ok (.value 0x8000)

-- A `float<2,1>` takes one byte, its top 4 bits zero: an `i8` load of it
-- gives its bits, and a float load of a byte ignores the top 4 bits.
#guard (let (p, S) := alloc (.float 2 1) 1 none 0
  outcomeInt (do
    let _ ← (storeFloatRule lay id 2 1 none 0 (.value 0xf) (.value p) : M _)
    loadRule lay id 8 none 0 (.value p)) S) == .ok (.value 0x0f)
#guard (let (p, S) := alloc (.int 8) 1 none 0
  outcome (do
    let _ ← (storeRule lay id 8 none 0 (.value 0xa5) (.value p) : M _)
    loadFloatRule lay id 2 1 none 0 (.value p)) S) == .ok (.value 0x5)

-- The bytes of an `f32` are its bits, least significant first.
#guard (let (p, S) := alloc (.float 8 23) 1 none 0
  outcomeInt (do
    let _ ← (storeFloatRule lay id 8 23 none 0 (.value 0x7fc00001) (.value p) : M _)
    loadRule lay id 8 none 0 (.value (at_ p 3))) S) == .ok (.value 0x7f)

-- A float load from fresh memory, or from a pointer's fragments, is poison.
#guard (let (p, S) := alloc (.float 11 52) 1 none 0
  outcome (loadFloatRule lay id 11 52 none 0 (.value p) : M _) S) == .ok .poison
#guard (let (p, S) := alloc (.ptr 0) 1 none 0
  outcome (do
    let _ ← (storePtrRule lay id 0 none 0 (.value ⟨some 0, 0⟩) (.value p) : M _)
    loadFloatRule lay id 11 52 none 0 (.value p)) S) == .ok .poison

-- An `f64` is aligned to 8 by default, so an access at offset 4 is
-- misaligned unless it says `align(4)`; an `f32` in bytes is misaligned.
#guard (let (p, S) := alloc (.float 11 52) 2 none 0
  outcome (loadFloatRule lay id 11 52 none 0 (.value (at_ p 4)) : M _) S) ==
    .error "a misaligned access"
#guard (let (p, S) := alloc (.float 11 52) 2 none 0
  outcome (loadFloatRule lay id 11 52 (some 4) 0 (.value (at_ p 4)) : M _) S) == .ok .poison
#guard (let (p, S) := alloc (.int 8) 4 none 0
  outcome (loadFloatRule lay id 8 23 none 0 (.value p) : M _) S) == .error "a misaligned access"

-- A poison pointer, out of bounds and a freed allocation are UB.
#guard (let (_, S) := alloc (.float 8 23) 1 none 0
  outcome (loadFloatRule lay id 8 23 none 0 .poison : M _) S) ==
    .error "a load through a poison pointer"
#guard (let (p, S) := alloc (.float 8 23) 1 none 0
  outcome (do
    let _ ← (storeFloatRule lay id 8 23 none 0 (.value 0) .poison : M _)
    loadFloatRule lay id 8 23 none 0 (.value p)) S) == .error "a store through a poison pointer"
#guard (let (p, S) := alloc (.float 8 23) 1 none 0
  outcome (loadFloatRule lay id 8 23 none 0 (.value (at_ p 4)) : M _) S) ==
    .error "an access out of bounds"
#guard (let (p, S) := alloc (.float 8 23) 1 none 0
  outcome (loadFloatRule lay id 8 23 none 0 (.value p) : M _) S.exit) ==
    .error "an access to a freed allocation"

/-! # Axioms -/

/-- info: 'Fir.Core.loadFloat_memTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.loadFloat_memTotal

/-- info: 'Fir.Core.loadFloat_memMonotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.loadFloat_memMonotone

/-- info: 'Fir.Core.loadFloat_readsNot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.loadFloat_readsNot

/-- info: 'Fir.Core.loadFloat_memPropagates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.loadFloat_memPropagates

/-- info: 'Fir.Core.loadFloat_memReturnsOnDefined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.loadFloat_memReturnsOnDefined

/-- info: 'Fir.Core.loadFloat_finitelyMany' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.loadFloat_finitelyMany

/-- info: 'Fir.Core.storeFloat_memTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.storeFloat_memTotal

/-- info: 'Fir.Core.storeFloat_memMonotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.storeFloat_memMonotone

/-- info: 'Fir.Core.storeFloat_readsNot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.storeFloat_readsNot

/-- info: 'Fir.Core.storeFloat_memPropagates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.storeFloat_memPropagates

/-- info: 'Fir.Core.storeFloat_memReturnsOnDefined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.storeFloat_memReturnsOnDefined

/-- info: 'Fir.Core.storeFloat_finitelyMany' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.storeFloat_finitelyMany

/-- info: 'Fir.Core.storeFloat_makesNoPoison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.storeFloat_makesNoPoison

end FirTest.FloatAccess
