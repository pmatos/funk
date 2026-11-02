import FirTest.Modes

/-!
Tests of #16's ops on `FirRef.runBytes`, which computes what `fir-ref run`
writes: `icmp` with each of its ten predicates, and `select`, at `i1`,
`i7`, `i8`, `i33`, `i64`, `i128` and the widest type, on the boundary
values `0`, `1`, all ones (`-1`), the signed minimum and the signed
maximum, and on pairs whose signed order is not their unsigned order.
Neither op is UB. `icmp` propagates poison; `select` gives poison for a
poison condition and gives the value it chooses as it is, so a poison it
does not choose does not matter. `fir-ref run` takes no `poison` argument,
so the tests of poison operands run the same rules through `runIn`, and
others make poison with a broken flag.
-/

namespace FirTest

open Fir FirRef

/-- `@f(%a: T, %b: T) -> i1`, which returns `icmp P %a, %b`. -/
def icmpAt (p ty : String) : String :=
  body ("func @f(%a: " ++ ty ++ ", %b: " ++ ty ++ ") -> i1")
    ["^e:", "  %s: i1 = icmp " ++ p ++ " %a, %b @0", "  ret %s @0"]

/-- What `fir-ref run` reports on `icmp P %a, %b` at the type `ty`, for each
predicate `P` in the order of `Pred.all`. -/
def cmpAll (ty a b : String) : List RunReport :=
  Core.Pred.all.map fun p => runText (icmpAt p.name ty) "@f" [a, b]

/-- The reports of runs that return what the ten predicates give, in the
order of `Pred.all`, on two values in the order `s` read as signed and in
the order `u` read as unsigned. -/
def ordered (s u : Ordering) : List RunReport :=
  (Core.predResults s u).map fun r => returns [toString r]

/-! # `icmp` at every width -/

-- At `i1`, `true` is `-1` read as signed and `1` read as unsigned.
#guard cmpAll "i1" "true" "false" == ordered .lt .gt
#guard cmpAll "i1" "false" "true" == ordered .gt .lt
#guard cmpAll "i1" "true" "true" == ordered .eq .eq
#guard cmpAll "i1" "false" "false" == ordered .eq .eq
#guard cmpAll "i7" "-1" "0" == ordered .lt .gt
#guard cmpAll "i7" "-64" "63" == ordered .lt .gt
#guard cmpAll "i7" "63" "-1" == ordered .gt .lt
#guard cmpAll "i7" "0" "1" == ordered .lt .lt
#guard cmpAll "i7" "-64" "-1" == ordered .lt .lt
#guard cmpAll "i7" "-64" "-64" == ordered .eq .eq
#guard cmpAll "i8" "-1" "1" == ordered .lt .gt
#guard cmpAll "i8" "-128" "127" == ordered .lt .gt
#guard cmpAll "i8" "127" "-128" == ordered .gt .lt
#guard cmpAll "i8" "-128" "0" == ordered .lt .gt
#guard cmpAll "i8" "1" "127" == ordered .lt .lt
#guard cmpAll "i8" "-1" "-1" == ordered .eq .eq
#guard cmpAll "i33" "-4294967296" "4294967295" == ordered .lt .gt
#guard cmpAll "i33" "0" "-1" == ordered .gt .lt
#guard cmpAll "i33" "-4294967296" "-1" == ordered .lt .lt
#guard cmpAll "i33" "4294967295" "4294967295" == ordered .eq .eq
#guard cmpAll "i64" "-9223372036854775808" "9223372036854775807" == ordered .lt .gt
#guard cmpAll "i64" "9223372036854775807" "-1" == ordered .gt .lt
#guard cmpAll "i64" "1" "0" == ordered .gt .gt
#guard cmpAll "i64" "-9223372036854775808" "-9223372036854775808" == ordered .eq .eq
#guard cmpAll "i128" "-170141183460469231731687303715884105728"
  "170141183460469231731687303715884105727" == ordered .lt .gt
#guard cmpAll "i128" "-1" "1" == ordered .lt .gt
#guard cmpAll "i128" "0" "0" == ordered .eq .eq
-- At the widest type, the signed minimum and maximum have over five
-- million decimal digits, so they are not spelled here; the tests of
-- `icmpValues` in the spec compare them at the other widths.
#guard cmpAll "i16777215" "-1" "1" == ordered .lt .gt
#guard cmpAll "i16777215" "0" "-1" == ordered .gt .lt
#guard cmpAll "i16777215" "-1" "-1" == ordered .eq .eq

/-! # `select` at every width -/

/-- `@f(%c: i1, %a: T, %b: T) -> T`, which returns `select %c, %a, %b`. -/
def selectAt (ty : String) : String :=
  body ("func @f(%c: i1, %a: " ++ ty ++ ", %b: " ++ ty ++ ") -> " ++ ty)
    ["^e:", "  %s: " ++ ty ++ " = select %c, %a, %b @0", "  ret %s @0"]

/-- Each width with two of its values. -/
def selectWidths : List (String × String × String) :=
  [("i1", "true", "false"), ("i7", "-64", "63"), ("i8", "-128", "127"),
   ("i33", "-4294967296", "4294967295"), ("i64", "-9223372036854775808", "9223372036854775807"),
   ("i128", "-170141183460469231731687303715884105728", "-1"), ("i16777215", "-1", "1")]

-- `true` chooses the first value and `false` the second.
#guard selectWidths.all fun (ty, a, b) =>
  runText (selectAt ty) "@f" ["true", a, b] == returns [a] &&
    runText (selectAt ty) "@f" ["false", a, b] == returns [b]

/-! # Poison

`runIn` takes `poison` as an argument, which `fir-ref run` does not. -/

-- A poison operand of `icmp` gives poison, in either place.
#guard Core.Pred.all.all fun p =>
  runIn inferInstance (icmpAt p.name "i8") ["poison", "0"] == some (returns ["poison"]) &&
    runIn inferInstance (icmpAt p.name "i1") ["true", "poison"] == some (returns ["poison"]) &&
    runIn inferInstance (icmpAt p.name "i64") ["poison", "poison"] == some (returns ["poison"])
#guard selectWidths.all fun (ty, a, b) =>
  -- A poison condition gives poison.
  runIn inferInstance (selectAt ty) ["poison", a, b] == some (returns ["poison"]) &&
    runIn inferInstance (selectAt ty) ["poison", a, a] == some (returns ["poison"]) &&
    -- The value not chosen does not matter, even when it is poison.
    runIn inferInstance (selectAt ty) ["true", a, "poison"] == some (returns [a]) &&
    runIn inferInstance (selectAt ty) ["false", "poison", b] == some (returns [b]) &&
    -- The value chosen is given as it is, poison included.
    runIn inferInstance (selectAt ty) ["true", "poison", b] == some (returns ["poison"]) &&
    runIn inferInstance (selectAt ty) ["false", a, "poison"] == some (returns ["poison"])
-- A broken flag gives poison: `icmp` propagates it, so a `select` on it
-- gives poison even when both values are the same, and a `select` that
-- does not choose it gives the other value.
#guard runText (body "func @f(%a: i8, %c: i1) -> i1, i8, i8, i8"
    ["^e:", "  %p: i8 = add nsw %a, %a @0", "  %e: i1 = icmp eq %p, %p @0",
     "  %s: i8 = select %e, %a, %a @0", "  %t: i8 = select %c, %p, %a @0",
     "  %u: i8 = select %c, %a, %p @0", "  ret %e, %s, %t, %u @0"]) "@f" ["100", "false"] ==
  returns ["poison", "poison", "100", "poison"]

/-! # A frozen poison

Every use of `%f` sees the same bits, so `icmp eq %f, %f` is `true`; a
`select` on a frozen condition may choose either value. -/

/-- `@f(%a: T) -> i1`, which freezes `add nsw %a, 1` once, as `%f`, and
returns `icmp eq %f, %f`. -/
def eqSelf (ty : String) : String :=
  body ("func @f(%a: " ++ ty ++ ") -> i1")
    ["^e:", "  %m: " ++ ty ++ " = const 1 @0", "  %p: " ++ ty ++ " = add nsw %a, %m @0",
     "  %f: " ++ ty ++ " = freeze %p @0", "  %d: i1 = icmp eq %f, %f @0", "  ret %d @0"]

#guard runText (eqSelf "i64") "@f" ["9223372036854775807"] (mode := .scripted ["5"]) ==
  returns ["true"] 1
#guard explore (eqSelf "i64") ["9223372036854775807"] ==
  { out := "{\"kind\":\"choice-budget-exceeded\",\"budget\":16}", status := 0 }
#guard explore (eqSelf "i8") ["127"] == outcomes [ret ["true"]] 1
#guard explore (body "func @f(%a: i1, %x: i8, %y: i8) -> i8"
    ["^e:", "  %p: i1 = add nsw %a, %a @0", "  %f: i1 = freeze %p @0",
     "  %s: i8 = select %f, %x, %y @0", "  ret %s @0"]) ["true", "1", "2"] ==
  outcomes [ret ["2"], ret ["1"]] 1

/-! # `select %c, %x, false` is not `and %c, %x`

Where `%x` may be poison, `and %c, %x` is not a sound rewrite of
`select %c, %x, false`: when `%c` is `false`, the `select` gives `false`
and the `and` gives poison, which `false` does not allow. `and %c, %g`,
with `%g = freeze %x`, is sound. `%x` is `add nsw %a, %b` at `i1`, where
`true` is `-1`: it is `false` when `%a` and `%b` are both `false`, `true`
when exactly one is `true`, and poison when both are `true`, since
`-1 + -1` overflows. The tests run all eight inputs. #16's corpus stage
tests this rewrite with the harness. -/

/-- `@f(%c: i1, %a: i1, %b: i1) -> i1`, which runs `lines` on `%c` and
`%x = add nsw %a, %b`, and returns their `%s`. -/
def rewritten (lines : List String) : String :=
  body "func @f(%c: i1, %a: i1, %b: i1) -> i1"
    (["^e:", "  %x: i1 = add nsw %a, %b @0", "  %z: i1 = const false @0"] ++ lines ++
      ["  ret %s @0"])

/-- The source: `select %c, %x, false`. -/
def selectForm : String := rewritten ["  %s: i1 = select %c, %x, %z @0"]

/-- The wrong rewrite: `and %c, %x`. -/
def andForm : String := rewritten ["  %s: i1 = and %c, %x @0"]

/-- The sound rewrite: `and %c, %g` with `%g = freeze %x`. -/
def frozenAndForm : String := rewritten ["  %g: i1 = freeze %x @0", "  %s: i1 = and %c, %g @0"]

-- Where `%c` is `false` and `%x` is poison, the `and` gives poison and the
-- `select` only `false`: the rewrite is wrong. `and %c, %g` gives `false`.
#guard explore selectForm ["false", "true", "true"] == outcomes [ret ["false"]] 0
#guard explore andForm ["false", "true", "true"] == outcomes [ret ["poison"]] 0
#guard explore frozenAndForm ["false", "true", "true"] == outcomes [ret ["false"]] 1
-- Where `%c` is `true` and `%x` is poison, the `select` gives poison, which
-- allows every outcome of both rewrites.
#guard explore selectForm ["true", "true", "true"] == outcomes [ret ["poison"]] 0
#guard explore andForm ["true", "true", "true"] == outcomes [ret ["poison"]] 0
#guard explore frozenAndForm ["true", "true", "true"] == outcomes [ret ["false"], ret ["true"]] 1
-- Where `%x` is not poison, all three give the same value: `true` where `%c`
-- and `%x` are both `true`, and `false` elsewhere.
#guard [(["false", "false", "false"], "false"), (["false", "false", "true"], "false"),
    (["false", "true", "false"], "false"), (["true", "false", "false"], "false"),
    (["true", "false", "true"], "true"), (["true", "true", "false"], "true")].all
  fun (args, v) => [selectForm, andForm, frozenAndForm].all fun t =>
    explore t args == outcomes [ret [v]] 0

/-! # The obligations' axioms -/

/-- info: 'Fir.Core.icmp_propagatesPoison' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.icmp_propagatesPoison

/-- info: 'Fir.Core.icmp_returnsOnDefined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.icmp_returnsOnDefined

/-- info: 'Fir.Core.icmp_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.icmp_total

/-- info: 'Fir.Core.icmp_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.icmp_monotone

/-- info: 'Fir.Core.select_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.select_total

/-- info: 'Fir.Core.select_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.select_monotone

end FirTest
