import FirTest.Modes
import FirTest.ValidateOps

/-!
Tests of #231's pointer offset `ptradd`. Its rule is checked on concrete
pointers in `Fir/Core/Pointer.lean`, and its laws are proved; these check
it through `FirRef.runBytes`, which computes what `fir-ref run` writes, and
through validation. A run starts with no allocation, so its only pointer
argument is poison, and `ptradd` of poison is poison, at every width of the
integer and in every memory. They also check that `ptradd` takes no choice,
in exhaustive mode, that a pointer it gives is one of its operand's memory,
and that a text whose types do not fit does not decode.
-/

namespace FirTest

open Fir FirRef

/-- `@f(%p: P, %k: K) -> P`, which returns `ptradd %p, %k`. -/
def ptraddText (ptr int : String) : String :=
  body ("func @f(%p: " ++ ptr ++ ", %k: " ++ int ++ ") -> " ++ ptr)
    ["^e:", "  %q: " ++ ptr ++ " = ptradd %p, %k @0", "  ret %q @0"]

/-- The layout line of a module with memory 1, of 16-bit units and 32-bit
pointers. -/
def memoryOne : String := "layout memory(1, unit(16), pointer(32), little)\n\n"

-- A poison pointer gives poison, whatever the integer, at every width.
#guard ["i1", "i8", "i33", "i64", "i128"].all fun t =>
  runText (ptraddText "ptr" t) "@f" ["poison", if t == "i1" then "true" else "-1"] ==
    returns ["poison"]
#guard runText (ptraddText "ptr" "i64") "@f" ["poison", "poison"] == returns ["poison"]
-- In another memory too.
#guard runText (memoryOne ++ ptraddText "ptr(1)" "i16") "@f" ["poison", "3"] == returns ["poison"]
-- `ptradd` chooses nothing: exhaustive mode finds one outcome.
#guard explore (ptraddText "ptr" "i8") ["poison", "5"] == outcomes [ret ["poison"]] 0
-- Offsets compose: two moves of a pointer, the second by the first's
-- integer negated.
#guard runText (body "func @f(%p: ptr, %k: i64) -> ptr"
    ["^e:", "  %q: ptr = ptradd %p, %k @0", "  %z: i64 = const 0 @0", "  %n: i64 = sub %z, %k @0",
     "  %r: ptr = ptradd %q, %n @0", "  ret %r @0"]) "@f" ["poison", "8"] == returns ["poison"]

-- Valid in each memory the module has, at any width of the integer.
#guard valid (ptraddText "ptr" "i1") && valid (ptraddText "ptr" "i128")
#guard valid (memoryOne ++ ptraddText "ptr(1)" "i64")
-- A pointer of a memory that the layout does not declare is not valid.
#guard checks (ptraddText "ptr(1)" "i64")
  ["a type names memory 1, which the data layout does not declare"]

/-- `@f(%p: P, %k: K) -> R`, whose one op is `%q: R = ptradd OPERANDS`. -/
def ptraddShape (p k r operands : String) : String :=
  body ("func @f(%p: " ++ p ++ ", %k: " ++ k ++ ") -> " ++ r)
    ["^e:", "  %q: " ++ r ++ " = ptradd " ++ operands ++ " @0", "  ret %q @0"]

-- Types that do not fit do not decode: a result of another memory, an
-- integer result, the operands swapped, a pointer or a float as the
-- offset, an attribute, or a third operand.
#guard [ptraddShape "ptr" "i64" "ptr(1)" "%p, %k", ptraddShape "ptr" "i64" "i64" "%p, %k",
  ptraddShape "ptr" "i64" "ptr" "%k, %p", ptraddShape "ptr" "ptr" "ptr" "%p, %k",
  ptraddShape "ptr" "f32" "ptr" "%p, %k", ptraddShape "ptr" "i64" "ptr" "inbounds %p, %k",
  ptraddShape "ptr" "i64" "ptr" "%p, %k, %k"].all
    fun t => (runText t "@f" ["poison", "0"]).status == 1

end FirTest
