import FirTest.Modes

/-!
Tests of #15's ops on `FirRef.runBytes`, which computes what `fir-ref run`
writes: `and`, `or`, `xor`, `shl`, `lshr` and `ashr` at `i1`, `i7`, `i8`,
`i33`, `i64`, `i128` and the widest type, on the boundary values `0`, `1`,
all ones (`-1`), the signed minimum and the signed maximum, and the shift
amounts `0`, `1`, `N - 1`, `N` and more. A shift by `N` or more gives
poison, as does a poison operand, and the function returns it. None of
these ops is UB. `xor %f, %f` of a frozen poison gives `0`, since every use
of `%f` sees the same bits. A flag on any of them does not decode.
-/

namespace FirTest

open Fir FirRef

/-! # Bitwise ops -/

-- At `i1`, `true` and `false` are the boolean values.
#guard bin "and" "i1" "true" "true" == returns ["true"]
#guard bin "and" "i1" "true" "false" == returns ["false"]
#guard bin "or" "i1" "false" "false" == returns ["false"]
#guard bin "or" "i1" "false" "true" == returns ["true"]
#guard bin "xor" "i1" "true" "true" == returns ["false"]
#guard bin "xor" "i1" "false" "true" == returns ["true"]
#guard bin "and" "i7" "-64" "63" == returns ["0"]
#guard bin "or" "i7" "-64" "63" == returns ["-1"]
#guard bin "xor" "i7" "-1" "63" == returns ["-64"]
#guard bin "and" "i8" "-1" "-128" == returns ["-128"]
#guard bin "or" "i8" "0" "1" == returns ["1"]
#guard bin "xor" "i8" "127" "-1" == returns ["-128"]
#guard bin "and" "i33" "-4294967296" "4294967295" == returns ["0"]
#guard bin "or" "i33" "-4294967296" "4294967295" == returns ["-1"]
#guard bin "xor" "i33" "-1" "1" == returns ["-2"]
#guard bin "and" "i64" "9223372036854775807" "-1" == returns ["9223372036854775807"]
#guard bin "or" "i64" "-9223372036854775808" "1" == returns ["-9223372036854775807"]
#guard bin "xor" "i64" "-9223372036854775808" "9223372036854775807" == returns ["-1"]
#guard bin "xor" "i128" "-170141183460469231731687303715884105728" "-1" ==
  returns ["170141183460469231731687303715884105727"]
#guard bin "and" "i128" "-170141183460469231731687303715884105728" "-1" ==
  returns ["-170141183460469231731687303715884105728"]
#guard bin "or" "i128" "-170141183460469231731687303715884105728"
  "170141183460469231731687303715884105727" == returns ["-1"]
#guard bin "or" "i16777215" "-1" "0" == returns ["-1"]
#guard bin "and" "i16777215" "-1" "1" == returns ["1"]
#guard bin "xor" "i16777215" "-1" "1" == returns ["-2"]

/-! # Shifts

The amount is read as unsigned: `N` or more gives poison, and so does an
amount whose top bit is set, such as `-1`. -/

-- At `i1`, an amount of `false` gives the value, and `true`, which is
-- `N`, gives poison.
#guard ["shl", "lshr", "ashr"].all fun op =>
  bin op "i1" "true" "false" == returns ["true"] &&
    bin op "i1" "false" "false" == returns ["false"] &&
    bin op "i1" "true" "true" == returns ["poison"] &&
    bin op "i1" "false" "true" == returns ["poison"]
#guard bin "shl" "i7" "1" "6" == returns ["-64"]
#guard bin "lshr" "i7" "-64" "6" == returns ["1"]
#guard bin "ashr" "i7" "-64" "6" == returns ["-1"]
#guard bin "ashr" "i7" "63" "1" == returns ["31"]
#guard bin "shl" "i8" "1" "7" == returns ["-128"]
#guard bin "shl" "i8" "127" "1" == returns ["-2"]
#guard bin "shl" "i8" "-1" "0" == returns ["-1"]
#guard bin "lshr" "i8" "-1" "1" == returns ["127"]
#guard bin "lshr" "i8" "-128" "7" == returns ["1"]
#guard bin "ashr" "i8" "-128" "7" == returns ["-1"]
#guard bin "ashr" "i8" "-128" "1" == returns ["-64"]
#guard bin "ashr" "i8" "127" "7" == returns ["0"]
#guard bin "shl" "i33" "1" "32" == returns ["-4294967296"]
#guard bin "lshr" "i33" "-1" "1" == returns ["4294967295"]
#guard bin "ashr" "i33" "-4294967296" "32" == returns ["-1"]
#guard bin "shl" "i64" "1" "63" == returns ["-9223372036854775808"]
#guard bin "lshr" "i64" "-9223372036854775808" "63" == returns ["1"]
#guard bin "ashr" "i64" "-9223372036854775808" "63" == returns ["-1"]
#guard bin "ashr" "i64" "9223372036854775807" "62" == returns ["1"]
#guard bin "shl" "i128" "1" "127" == returns ["-170141183460469231731687303715884105728"]
#guard bin "lshr" "i128" "-1" "127" == returns ["1"]
#guard bin "ashr" "i128" "-170141183460469231731687303715884105728" "127" == returns ["-1"]
#guard bin "shl" "i16777215" "-1" "1" == returns ["-2"]
#guard bin "lshr" "i16777215" "-1" "16777214" == returns ["1"]
#guard bin "ashr" "i16777215" "-1" "16777214" == returns ["-1"]
-- An amount of `N`, more than `N`, the signed minimum or `-1` gives
-- poison, at every width. At `i16777215` the signed minimum has over five
-- million decimal digits, so it is not spelled here: `shiftValues_msb`
-- proves that it gives poison at every width.
#guard ["shl", "lshr", "ashr"].all fun op =>
  ["7", "8", "-64", "-1"].all (bin op "i7" "1" · == returns ["poison"]) &&
    ["8", "9", "-128", "-1"].all (bin op "i8" "-1" · == returns ["poison"]) &&
    ["33", "34", "-4294967296", "-1"].all (bin op "i33" "1" · == returns ["poison"]) &&
    ["64", "65", "-9223372036854775808", "-1"].all (bin op "i64" "-1" · == returns ["poison"]) &&
    ["128", "129", "-170141183460469231731687303715884105728", "-1"].all
      (bin op "i128" "1" · == returns ["poison"]) &&
    ["16777215", "16777216", "-1"].all (bin op "i16777215" "1" · == returns ["poison"])

/-! # Poison

`runIn` takes `poison` as an argument, which `fir-ref run` does not. -/

-- A poison operand, in either place, gives poison.
#guard ["and", "or", "xor", "shl", "lshr", "ashr"].all fun op =>
  runIn inferInstance (binAt op "i8") ["poison", "0"] == some (returns ["poison"]) &&
    runIn inferInstance (binAt op "i8") ["1", "poison"] == some (returns ["poison"]) &&
    runIn inferInstance (binAt op "i1") ["poison", "poison"] == some (returns ["poison"]) &&
    runIn inferInstance (binAt op "i64") ["poison", "64"] == some (returns ["poison"])
-- A broken flag gives poison, and it propagates through these ops, even
-- where a value in its place would decide the result, as `and` with `0`
-- and `or` with `-1` would.
#guard runText (body "func @f(%a: i8) -> i8, i8, i8"
    ["^e:", "  %z: i8 = const 0 @0", "  %o: i8 = const -1 @0", "  %p: i8 = add nsw %a, %a @0",
     "  %x: i8 = and %p, %z @0", "  %y: i8 = or %o, %p @0", "  %s: i8 = shl %z, %p @0",
     "  ret %x, %y, %s @0"]) "@f" ["100"] == returns ["poison", "poison", "poison"]
-- A shift by `N` gives poison, which the next op propagates.
#guard runText (body "func @f(%a: i8) -> i8"
    ["^e:", "  %n: i8 = const 8 @0", "  %s: i8 = lshr %a, %n @0", "  %x: i8 = xor %s, %s @0",
     "  ret %x @0"]) "@f" ["1"] == returns ["poison"]

/-! # `xor` of a frozen poison

Every use of `%f` sees the same bits, so `xor %f, %f` is `0`. -/

/-- `@f(%a: T) -> T`, which freezes `add nsw %a, 1` once, as `%f`, and
returns `xor %f, %f`. -/
def xorSelf (ty : String) : String :=
  body ("func @f(%a: " ++ ty ++ ") -> " ++ ty)
    ["^e:", "  %m: " ++ ty ++ " = const 1 @0", "  %p: " ++ ty ++ " = add nsw %a, %m @0",
     "  %f: " ++ ty ++ " = freeze %p @0", "  %d: " ++ ty ++ " = xor %f, %f @0", "  ret %d @0"]

#guard runText (xorSelf "i64") "@f" ["9223372036854775807"] (mode := .scripted ["5"]) ==
  returns ["0"] 1
#guard runText (xorSelf "i64") "@f" ["9223372036854775807"] (mode := .scripted ["-1"]) ==
  returns ["0"] 1
#guard explore (xorSelf "i64") ["9223372036854775807"] ==
  { out := "{\"kind\":\"choice-budget-exceeded\",\"budget\":16}", status := 0 }
#guard explore (xorSelf "i8") ["127"] == outcomes [ret ["0"]] 1

/-! # No flags

The spec gives these ops no flags, so a flag on one does not decode. -/

#guard ["and", "or", "xor", "shl", "lshr", "ashr"].all fun op =>
  ["nuw", "nsw", "exact"].all fun f =>
    Core.Op.decode op [.word f] [.int 8, .int 8] [.int 8] == none &&
      (bin (op ++ " " ++ f) "i8" "1" "1").status == 1

/-! # The obligations' axioms -/

/-- info: 'Fir.Core.shiftValues_msb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.shiftValues_msb

/-- info: 'Fir.Core.and_propagatesPoison' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.and_propagatesPoison

/-- info: 'Fir.Core.and_returnsOnDefined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.and_returnsOnDefined

/-- info: 'Fir.Core.and_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.and_total

/-- info: 'Fir.Core.and_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.and_monotone

/-- info: 'Fir.Core.or_propagatesPoison' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.or_propagatesPoison

/-- info: 'Fir.Core.or_returnsOnDefined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.or_returnsOnDefined

/-- info: 'Fir.Core.or_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.or_total

/-- info: 'Fir.Core.or_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.or_monotone

/-- info: 'Fir.Core.xor_propagatesPoison' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.xor_propagatesPoison

/-- info: 'Fir.Core.xor_returnsOnDefined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.xor_returnsOnDefined

/-- info: 'Fir.Core.xor_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.xor_total

/-- info: 'Fir.Core.xor_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.xor_monotone

/-- info: 'Fir.Core.shl_propagatesPoison' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.shl_propagatesPoison

/-- info: 'Fir.Core.shl_returnsOnDefined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.shl_returnsOnDefined

/-- info: 'Fir.Core.shl_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.shl_total

/-- info: 'Fir.Core.shl_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.shl_monotone

/-- info: 'Fir.Core.lshr_propagatesPoison' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.lshr_propagatesPoison

/-- info: 'Fir.Core.lshr_returnsOnDefined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.lshr_returnsOnDefined

/-- info: 'Fir.Core.lshr_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.lshr_total

/-- info: 'Fir.Core.lshr_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.lshr_monotone

/-- info: 'Fir.Core.ashr_propagatesPoison' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.ashr_propagatesPoison

/-- info: 'Fir.Core.ashr_returnsOnDefined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.ashr_returnsOnDefined

/-- info: 'Fir.Core.ashr_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.ashr_total

/-- info: 'Fir.Core.ashr_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.ashr_monotone

end FirTest
