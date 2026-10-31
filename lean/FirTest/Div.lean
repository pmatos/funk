import FirTest.Modes

/-!
Tests of #18's ops on `FirRef.runBytes`, which computes what `fir-ref run`
writes: `sdiv`, `udiv`, `srem` and `urem`, with and without `exact`, at
`i1`, `i7`, `i8`, `i33`, `i64`, `i128` and `i16777215`, with the boundary
values; their immediate UB, each with its reason, which ends the run; the
poison that `exact` and a poison dividend give; and a frozen divisor that
may be zero, in both modes. `fir-ref run` takes no `poison` argument, so the
tests of poison operands run the same rules through `runIn`, whose
arguments may be `poison`.
-/

namespace FirTest

open Fir FirRef

/-- The report of a run that hits UB for `reason`, after `c` choices. -/
def ubBy (reason : String) (c : Nat := 0) : RunReport :=
  { out := "{\"kind\":\"ub\",\"reason\":\"" ++ reason ++ "\",\"choices\":" ++ toString c ++ "}",
    status := 0 }

/-- What `fir-ref run`'s rules give on `OP %a, %b` at the type `ty`, on
arguments that may be `poison`. -/
def binP (op ty a b : String) : Option RunReport := runIn inferInstance (binAt op ty) [a, b]

/-! # Values -/

#guard bin "sdiv" "i8" "-7" "2" == returns ["-3"]
#guard bin "sdiv" "i8" "7" "-2" == returns ["-3"]
#guard bin "sdiv" "i8" "-128" "1" == returns ["-128"]
#guard bin "sdiv" "i8" "127" "-1" == returns ["-127"]
#guard bin "sdiv" "i1" "false" "true" == returns ["false"]
#guard bin "sdiv" "i7" "63" "-1" == returns ["-63"]
#guard bin "sdiv" "i33" "-4294967296" "2" == returns ["-2147483648"]
#guard bin "sdiv" "i64" "9223372036854775807" "-1" == returns ["-9223372036854775807"]
#guard bin "sdiv" "i64" "-1" "-9223372036854775808" == returns ["0"]
#guard bin "sdiv" "i128" "-170141183460469231731687303715884105728" "2" ==
  returns ["-85070591730234615865843651857942052864"]
#guard bin "sdiv" "i16777215" "-1" "-1" == returns ["1"]
#guard bin "udiv" "i8" "-1" "2" == returns ["127"]
#guard bin "udiv" "i8" "-128" "-1" == returns ["0"]
#guard bin "udiv" "i1" "true" "true" == returns ["true"]
#guard bin "udiv" "i7" "-1" "2" == returns ["63"]
#guard bin "udiv" "i33" "-1" "-4294967296" == returns ["1"]
#guard bin "udiv" "i64" "-1" "-9223372036854775808" == returns ["1"]
#guard bin "udiv" "i128" "-1" "-1" == returns ["1"]
#guard bin "srem" "i8" "-7" "2" == returns ["-1"]
#guard bin "srem" "i8" "7" "-2" == returns ["1"]
#guard bin "srem" "i8" "127" "-1" == returns ["0"]
#guard bin "srem" "i1" "false" "true" == returns ["false"]
#guard bin "srem" "i7" "-64" "63" == returns ["-1"]
#guard bin "srem" "i33" "-4294967296" "4294967295" == returns ["-1"]
#guard bin "srem" "i64" "-9223372036854775808" "9223372036854775807" == returns ["-1"]
#guard bin "srem" "i128" "-170141183460469231731687303715884105728" "3" == returns ["-2"]
#guard bin "urem" "i8" "-1" "-1" == returns ["0"]
#guard bin "urem" "i8" "-128" "-1" == returns ["-128"]
#guard bin "urem" "i1" "true" "true" == returns ["false"]
#guard bin "urem" "i7" "-64" "63" == returns ["1"]
#guard bin "urem" "i33" "-1" "-4294967296" == returns ["4294967295"]
#guard bin "urem" "i64" "-9223372036854775808" "9223372036854775807" == returns ["1"]
#guard bin "urem" "i16777215" "-1" "2" == returns ["1"]

/-! # `exact` -/

#guard bin "sdiv exact" "i8" "-6" "3" == returns ["-2"]
#guard bin "sdiv exact" "i8" "7" "2" == returns ["poison"]
#guard bin "sdiv exact" "i8" "-128" "2" == returns ["-64"]
#guard bin "sdiv exact" "i1" "false" "true" == returns ["false"]
#guard bin "sdiv exact" "i7" "63" "2" == returns ["poison"]
#guard bin "sdiv exact" "i33" "4294967295" "-1" == returns ["-4294967295"]
#guard bin "sdiv exact" "i64" "-9223372036854775808" "9223372036854775807" == returns ["poison"]
#guard bin "udiv exact" "i8" "-2" "2" == returns ["127"]
#guard bin "udiv exact" "i8" "-2" "-1" == returns ["poison"]
#guard bin "udiv exact" "i1" "true" "true" == returns ["true"]
#guard bin "udiv exact" "i7" "-2" "63" == returns ["2"]
#guard bin "udiv exact" "i33" "4294967295" "-1" == returns ["poison"]
#guard bin "udiv exact" "i128" "-1" "2" == returns ["poison"]

/-! # UB

Each UB names its op and its case. At `i1`, `true` is the signed minimum and
`-1`, so `sdiv` and `srem` of `true` by `true` are UB. -/

#guard bin "sdiv" "i8" "-128" "-1" == ubBy "sdiv of the signed minimum by -1"
#guard bin "sdiv exact" "i8" "-128" "-1" == ubBy "sdiv of the signed minimum by -1"
#guard bin "sdiv" "i1" "true" "true" == ubBy "sdiv of the signed minimum by -1"
#guard bin "sdiv" "i7" "-64" "-1" == ubBy "sdiv of the signed minimum by -1"
#guard bin "sdiv" "i33" "-4294967296" "-1" == ubBy "sdiv of the signed minimum by -1"
#guard bin "sdiv" "i64" "-9223372036854775808" "-1" == ubBy "sdiv of the signed minimum by -1"
#guard bin "sdiv" "i128" "-170141183460469231731687303715884105728" "-1" ==
  ubBy "sdiv of the signed minimum by -1"
#guard bin "srem" "i8" "-128" "-1" == ubBy "srem of the signed minimum by -1"
#guard bin "srem" "i1" "true" "true" == ubBy "srem of the signed minimum by -1"
#guard bin "srem" "i64" "-9223372036854775808" "-1" == ubBy "srem of the signed minimum by -1"
#guard bin "sdiv" "i8" "5" "0" == ubBy "sdiv by zero"
#guard bin "sdiv exact" "i64" "0" "0" == ubBy "sdiv by zero"
#guard bin "udiv" "i1" "true" "false" == ubBy "udiv by zero"
#guard bin "udiv exact" "i7" "-1" "0" == ubBy "udiv by zero"
#guard bin "srem" "i33" "1" "0" == ubBy "srem by zero"
#guard bin "urem" "i128" "-1" "0" == ubBy "urem by zero"
#guard bin "urem" "i16777215" "1" "0" == ubBy "urem by zero"
-- UB ends the run: the op after it is not run.
#guard runText (body "func @f(%a: i8, %b: i8) -> i8"
    ["^e:", "  %q: i8 = udiv %a, %b @0", "  %r: i8 = and %q, %q @0", "  ret %r @0"]) "@f"
    ["1", "0"] == ubBy "udiv by zero"

/-! # Poison operands

A poison divisor is UB, and so is a poison dividend of `sdiv` or `srem` by
`-1`. Otherwise a poison dividend gives poison, `udiv` and `urem` by all
ones included. -/

#guard binP "sdiv" "i8" "5" "poison" == some (ubBy "sdiv by poison")
#guard binP "sdiv exact" "i8" "poison" "poison" == some (ubBy "sdiv by poison")
#guard binP "udiv" "i1" "true" "poison" == some (ubBy "udiv by poison")
#guard binP "srem" "i33" "poison" "poison" == some (ubBy "srem by poison")
#guard binP "urem" "i64" "0" "poison" == some (ubBy "urem by poison")
#guard binP "sdiv" "i8" "poison" "-1" == some (ubBy "sdiv of poison by -1")
#guard binP "sdiv exact" "i64" "poison" "-1" == some (ubBy "sdiv of poison by -1")
#guard binP "sdiv" "i1" "poison" "true" == some (ubBy "sdiv of poison by -1")
#guard binP "srem" "i7" "poison" "-1" == some (ubBy "srem of poison by -1")
#guard binP "srem" "i128" "poison" "-1" == some (ubBy "srem of poison by -1")
#guard binP "sdiv" "i8" "poison" "0" == some (ubBy "sdiv by zero")
#guard binP "urem" "i8" "poison" "0" == some (ubBy "urem by zero")
#guard binP "sdiv" "i8" "poison" "2" == some (returns ["poison"])
#guard binP "sdiv exact" "i8" "poison" "3" == some (returns ["poison"])
#guard binP "srem" "i64" "poison" "-9223372036854775808" == some (returns ["poison"])
#guard binP "udiv" "i8" "poison" "-1" == some (returns ["poison"])
#guard binP "udiv exact" "i33" "poison" "-1" == some (returns ["poison"])
#guard binP "udiv" "i1" "poison" "true" == some (returns ["poison"])
#guard binP "urem" "i8" "poison" "-1" == some (returns ["poison"])
#guard binP "urem" "i1" "poison" "true" == some (returns ["poison"])

/-! # A frozen divisor that may be zero

`%f` freezes a poison, so it may be any value of `i2`, zero included.
Exhaustive mode lists the UB of a zero divisor among the outcomes, and
scripted mode reports it on the choice `0`. -/

/-- `@f(%a: i2, %b: i2) -> i2`, which returns `OP %a, %f`, where `%f`
freezes `add nsw %b, 1`, poison at `1`. -/
def frozenDivisor (op : String) : String :=
  body "func @f(%a: i2, %b: i2) -> i2"
    ["^e:", "  %m: i2 = const 1 @0", "  %p: i2 = add nsw %b, %m @0", "  %f: i2 = freeze %p @0",
     "  %q: i2 = " ++ op ++ " %a, %f @0", "  ret %q @0"]

#guard explore (frozenDivisor "udiv") ["-1", "1"] ==
  outcomes ["{\"kind\":\"ub\",\"reason\":\"udiv by zero\"}", ret ["-1"], ret ["1"]] 1
#guard explore (frozenDivisor "sdiv") ["-2", "1"] ==
  outcomes ["{\"kind\":\"ub\",\"reason\":\"sdiv by zero\"}", ret ["-2"], ret ["1"],
    "{\"kind\":\"ub\",\"reason\":\"sdiv of the signed minimum by -1\"}"] 1
#guard runText (frozenDivisor "urem") "@f" ["-1", "1"] (mode := .scripted ["0"]) ==
  ubBy "urem by zero" 1
#guard runText (frozenDivisor "urem") "@f" ["-1", "1"] (mode := .scripted ["-2"]) ==
  returns ["1"] 1
-- A divisor that is not poison is not frozen into zero.
#guard explore (frozenDivisor "srem") ["1", "0"] == outcomes [ret ["0"]] 0

/-! # The theorems' axioms -/

/-- info: 'Fir.Core.sdiv_propagatesPoison' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.sdiv_propagatesPoison

/-- info: 'Fir.Core.sdiv_returnsOnDefined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.sdiv_returnsOnDefined

/-- info: 'Fir.Core.sdiv_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.sdiv_total

/-- info: 'Fir.Core.sdiv_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.sdiv_monotone

/-- info: 'Fir.Core.udiv_propagatesPoison' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.udiv_propagatesPoison

/-- info: 'Fir.Core.udiv_returnsOnDefined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.udiv_returnsOnDefined

/-- info: 'Fir.Core.udiv_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.udiv_total

/-- info: 'Fir.Core.udiv_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.udiv_monotone

/-- info: 'Fir.Core.srem_propagatesPoison' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.srem_propagatesPoison

/-- info: 'Fir.Core.srem_returnsOnDefined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.srem_returnsOnDefined

/-- info: 'Fir.Core.srem_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.srem_total

/-- info: 'Fir.Core.srem_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.srem_monotone

/-- info: 'Fir.Core.urem_propagatesPoison' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.urem_propagatesPoison

/-- info: 'Fir.Core.urem_returnsOnDefined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.urem_returnsOnDefined

/-- info: 'Fir.Core.urem_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.urem_total

/-- info: 'Fir.Core.urem_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.urem_monotone

/-- info: 'Fir.Core.div_zero_width' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.div_zero_width

end FirTest
