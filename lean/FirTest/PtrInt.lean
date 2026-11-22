import FirTest.Div
import FirTest.Modes
import FirTest.ValidateOps

/-!
Tests of `ptrExpose` and `ptrFromInt` (#232), written `ptr_expose` and
`ptr_from_int`: their text, their rules with memory and `fir-ref run` on
whole functions, under the canonical layout and resolver that `fir-ref`
follows. A pointer exposed and turned back accesses its allocation; an
integer of the same address plus an offset accesses the same allocation at
that offset; an address that was never exposed gives a pointer with no
provenance, and an access through it is UB. A function whose result does
not depend on the address, a round trip through an integer, gives the same
result under every layout. Exposing a poison pointer is UB, and a poison
integer gives a poison pointer, so an access through it is UB. Then the
module's data layout: the integer is as wide as the memory's pointers, and
the memory is integral (the human's rulings of 2026-11-18 on #232, Q2, and
of 2026-11-11 on #231). Last, the axioms of the obligations that each op
meets.
-/

namespace FirTest.PtrInt

open Fir Fir.Core Fir.Memory FirRef

/-! # Text -/

-- Each op reads back from its spelling, in memory 0 and in memory 1.
#guard Op.decode "ptr_expose" [] [.ptr 0] [.int 64] == some (.ptrExpose 0 64)
#guard Op.decode "ptr_from_int" [] [.int 32] [.ptr 1] == some (.ptrFromInt 1 32)
#guard (Op.ptrExpose 0 64).name == "ptr_expose" && (Op.ptrFromInt 0 64).name == "ptr_from_int"
#guard (Op.ptrExpose 0 64).attrs.isEmpty && (Op.ptrFromInt 0 64).attrs.isEmpty

/-! # Rules with memory -/

/-- The lines of a block that holds `ops`, each at location `@0`. -/
def body (ops : List String) : String :=
  String.join (ops.map fun o => "  " ++ o ++ " @0\n")

/-- `@f(%x: i32) -> i32` stores `%x` in a stack slot of two `i32`, exposes
the slot, and takes `%a`, the address plus `off` bytes. After the ops
`pre`, it turns `src` back into a pointer and loads an `i32` through it. -/
def roundTrip (pre : List String) (src : String := "%a") (off : Int := 0) : String :=
  FirTest.oneFunc ("func @f(%x: i32) -> i32 {\n^entry:\n" ++ body ([
    "%p: ptr = alloca stack i32 2", "store nonatomic %x, %p", "%a0: i64 = ptr_expose %p",
    "%o: i64 = const " ++ toString off, "%a: i64 = add %a0, %o"] ++ pre ++
    ["%q: ptr = ptr_from_int " ++ src, "%v: i32 = load nonatomic %q", "ret %v"]) ++ "}\n")

-- A pointer exposed and turned back loads what its allocation holds.
#guard runText (roundTrip []) "@f" ["42"] == returns ["42"]
-- Through arithmetic that does not change the address, as a round trip
-- through an integer: xor twice with the same value.
#guard runText (roundTrip ["%k: i64 = const 255", "%b: i64 = xor %a, %k", "%c: i64 = xor %b, %k"]
  "%c") "@f" ["-7"] == returns ["-7"]
-- An address four bytes in is the second `i32` of the slot, which holds
-- poison until a store writes it.
#guard runText (roundTrip [] (off := 4)) "@f" ["42"] == returns ["poison"]
-- Eight bytes in is the slot's end: a pointer to it, and a load through it
-- is out of bounds.
#guard runText (roundTrip [] (off := 8)) "@f" ["42"] == ubBy "an access out of bounds"

/-- `@f() -> i32` turns the constant address `z` into a pointer and loads
an `i32` through it, after allocating and storing in a slot it never
exposes. -/
def never (z : Int) : String :=
  FirTest.oneFunc ("func @f() -> i32 {\n^entry:\n" ++ body [
    "%p: ptr = alloca stack i32", "%x: i32 = const 1", "store nonatomic %x, %p",
    "%a: i64 = const " ++ toString z, "%q: ptr = ptr_from_int %a",
    "%v: i32 = load nonatomic %q", "ret %v"] ++ "}\n")

-- An address that was never exposed gives no provenance: the address the
-- slot would get, 4, and address 0 alike.
#guard runText (never 4) "@f" [] == ubBy "an access through a pointer without provenance"
#guard runText (never 0) "@f" [] == ubBy "an access through a pointer without provenance"

/-- `@f(%a: i64) -> i32` loads an `i32` through the pointer that `%a`
turns into, after exposing a slot. -/
def fromArg : String :=
  FirTest.oneFunc ("func @f(%a: i64) -> i32 {\n^entry:\n" ++ body [
    "%p: ptr = alloca stack i32", "%e: i64 = ptr_expose %p",
    "%q: ptr = ptr_from_int %a", "%v: i32 = load nonatomic %q", "ret %v"] ++ "}\n")

-- A poison integer gives a poison pointer, and a load through it is UB.
#guard runText fromArg "@f" ["poison"] == ubBy "a load through a poison pointer"

/-- `@f(%x: i64) -> i64` exposes a pointer that `%x` turns into first, as
an integer that is poison when `%x` is. -/
def exposePoison : String :=
  FirTest.oneFunc ("func @f(%x: i64) -> i64 {\n^entry:\n" ++ body [
    "%q: ptr = ptr_from_int %x", "%a: i64 = ptr_expose %q", "ret %a"] ++ "}\n")

-- Exposing a poison pointer is UB.
#guard runText exposePoison "@f" ["poison"] == ubBy "a ptr_expose of a poison pointer"
-- Exposing a pointer with no provenance gives its offset, the integer it
-- came from.
#guard runText exposePoison "@f" ["77"] == returns ["77"]

/-! # The data layout -/

-- Each op asks the width of its memory's pointers; no other op asks one.
#guard Op.addrWidths (.ptrExpose 1 32) == [(1, 32)] && Op.addrWidths (.ptrFromInt 0 64) == [(0, 64)]
#guard (Op.addrWidths (.ptradd 0 64)).isEmpty

/-- Memory 1 of 32-bit pointers, non-integral when `ni` is true. -/
def mem1 (ni : Bool) : MemLayout :=
  { mem := 1, unit := 8, pointer := 32, order := .little, nonIntegral := ni }

#guard (DataLayout.HasAddrs [] (0, 64) : Bool)
#guard !(DataLayout.HasAddrs [] (0, 32) : Bool)
#guard (DataLayout.HasAddrs [mem1 false] (1, 32) : Bool)
#guard !(DataLayout.HasAddrs [mem1 true] (1, 32) : Bool)
#guard (addrsProblem [] "f" [(0, 64), (0, 32)]).map (·.message) ==
  some "an op turns pointers of memory 0 into integers of 32 bits or back, but its pointers have 64 bits"
#guard (addrsProblem [mem1 true] "f" [(1, 32)]).map (·.message) ==
  some "an op turns pointers of memory 1 into integers or back, but the memory is non-integral"
#guard (addrsProblem [] "f" [(0, 64)]).isNone

/-- A module of the layout line `lay` whose `@f` exposes a pointer of
`ptr` into an `int`, and turns an `int` back into a `ptr`. -/
def layoutCase (lay ptr int : String) : String :=
  lay ++ FirTest.oneFunc ("func @f(%p: " ++ ptr ++ ", %a: " ++ int ++ ") -> " ++ int ++
    " {\n^entry:\n  %b: " ++ int ++ " = ptr_expose %p @0\n  %q: " ++ ptr ++
    " = ptr_from_int %a @0\n  ret %b @0\n}\n")

#guard FirTest.valid (layoutCase "" "ptr" "i64")
#guard FirTest.valid (layoutCase "layout memory(1, unit(8), pointer(32), little)\n\n" "ptr(1)" "i32")
#guard FirTest.checks (layoutCase "" "ptr" "i32")
  ["an op turns pointers of memory 0 into integers of 32 bits or back, but its pointers have 64 bits"]
#guard FirTest.checks
  (layoutCase "layout memory(1, unit(8), pointer(32), little, nonintegral)\n\n" "ptr(1)" "i32")
  ["an op turns pointers of memory 1 into integers or back, but the memory is non-integral"]

/-! # Axioms -/

/-- info: 'Fir.Core.ptrExpose_memMonotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.ptrExpose_memMonotone

/-- info: 'Fir.Core.ptrFromInt_memMonotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.ptrFromInt_memMonotone

/-- info: 'Fir.Core.ptrFromInt_memPropagates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.ptrFromInt_memPropagates

/-- info: 'Fir.Core.lawfulDialectAddresses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.lawfulDialectAddresses

/-- info: 'Fir.Gpu.coreGpu_lawfulAddresses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Gpu.coreGpu_lawfulAddresses

end FirTest.PtrInt
