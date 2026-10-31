import FirTest.Interpreter

/-!
Tests of #14's ops and of `fir-ref run`'s exhaustive and scripted modes
(ADR-2026-10-30-2218), on `FirRef.runBytes`: `sub` and `mul`, the flags of
`add`, `sub` and `mul` at several widths, poison that a broken flag gives
and that propagates to the returned values, and `freeze`, whose choices
scripted mode takes from `--choices` and exhaustive mode tries in turn. A
choice sequence that does not fit the run is an error of its own, and so is
a run that chooses more bits than exhaustive mode's budget.
-/

namespace FirTest

open Fir FirRef

/-- `@f(%a: T, %b: T) -> T`, which returns `OP %a, %b`. -/
def binAt (op ty : String) : String :=
  body ("func @f(%a: " ++ ty ++ ", %b: " ++ ty ++ ") -> " ++ ty)
    ["^e:", "  %s: " ++ ty ++ " = " ++ op ++ " %a, %b @0", "  ret %s @0"]

/-- What `fir-ref run` reports on `OP %a, %b` at the type `ty`. -/
def bin (op ty a b : String) : RunReport := runText (binAt op ty) "@f" [a, b]

/-! # `sub`, `mul` and the flags -/

#guard bin "sub" "i8" "-128" "1" == returns ["127"]
#guard bin "sub" "i1" "false" "true" == returns ["true"]
#guard bin "mul" "i8" "16" "16" == returns ["0"]
#guard bin "mul" "i7" "-64" "-1" == returns ["-64"]
#guard bin "mul" "i33" "65536" "65536" == returns ["-4294967296"]
#guard bin "sub" "i128" "-170141183460469231731687303715884105728" "1" ==
  returns ["170141183460469231731687303715884105727"]
-- A broken flag gives poison, which the function returns.
#guard bin "add nsw" "i8" "127" "1" == returns ["poison"]
#guard bin "add nuw" "i8" "127" "1" == returns ["-128"]
#guard bin "add nuw" "i8" "-1" "1" == returns ["poison"]
#guard bin "add nuw nsw" "i8" "-1" "1" == returns ["poison"]
#guard bin "add nuw nsw" "i8" "100" "27" == returns ["127"]
#guard bin "sub nuw" "i8" "0" "1" == returns ["poison"]
#guard bin "sub nsw" "i8" "0" "1" == returns ["-1"]
#guard bin "sub nsw" "i64" "-9223372036854775808" "1" == returns ["poison"]
#guard bin "mul nsw" "i64" "-9223372036854775808" "-1" == returns ["poison"]
#guard bin "mul nuw" "i32" "65536" "65536" == returns ["poison"]
#guard bin "mul nuw nsw" "i16" "181" "181" == returns ["32761"]
#guard bin "mul nuw nsw" "i16" "182" "182" == returns ["poison"]
#guard bin "mul nuw nsw" "i16" "181" "-1" == returns ["poison"]
#guard bin "mul nsw" "i16" "181" "-1" == returns ["-181"]
#guard bin "add nsw" "i1" "true" "true" == returns ["poison"]
#guard bin "add nsw" "i1" "true" "false" == returns ["true"]
#guard bin "mul nsw" "i1" "true" "true" == returns ["poison"]
#guard bin "mul nuw" "i1" "true" "true" == returns ["true"]
#guard bin "sub nsw" "i7" "-64" "1" == returns ["poison"]
#guard bin "add nuw" "i33" "-1" "1" == returns ["poison"]
-- Poison propagates through `add`, `sub` and `mul`, whatever their flags.
#guard runText (body "func @f(%a: i8) -> i8, i8"
    ["^e:", "  %p: i8 = add nsw %a, %a @0", "  %q: i8 = mul nuw %p, %a @0",
     "  %r: i8 = sub %q, %q @0", "  ret %q, %r @0"]) "@f" ["100"] == returns ["poison", "poison"]

/-! # `freeze` in scripted mode

`%p` is poison when `%a + 1` overflows, as it does at `1` in `i2`, and
`%f` freezes it. With no choices, a run that chooses does not fit. -/

/-- `@f(%a: T) -> T`, which returns `freeze` of `add nsw %a, 1`, with `1`
spelled `one`. -/
def frozen (ty : String) (one : String := if ty == "i1" then "true" else "1") : String :=
  body ("func @f(%a: " ++ ty ++ ") -> " ++ ty)
    ["^e:", "  %m: " ++ ty ++ " = const " ++ one ++ " @0", "  %p: " ++ ty ++ " = add nsw %a, %m @0",
     "  %f: " ++ ty ++ " = freeze %p @0", "  ret %f @0"]

/-- What scripted mode reports on `frozen ty` at `a`, with the choices
`cs`. -/
def scripted (ty a : String) (cs : List String) : RunReport :=
  runText (frozen ty) "@f" [a] (mode := .scripted cs)

/-- The error of choices that do not fit the run. -/
def misfit (why : String) : RunReport :=
  fails 2 ("fir-ref: @f: the choices do not fit the run: " ++ why)

#guard scripted "i2" "1" ["-1"] == returns ["-1"] 1
#guard scripted "i2" "1" ["1"] == returns ["1"] 1
#guard scripted "i1" "true" ["false"] == returns ["false"] 1
#guard scripted "i7" "63" ["-64"] == returns ["-64"] 1
#guard scripted "i33" "4294967295" ["-4294967296"] == returns ["-4294967296"] 1
#guard scripted "i64" "9223372036854775807" ["42"] == returns ["42"] 1
-- `freeze` of a value gives it, with no choice.
#guard scripted "i2" "0" [] == returns ["1"]
#guard scripted "i64" "5" [] == returns ["6"]
-- Choices that do not fit: too few, too many, or not a value of the
-- choice's type.
#guard scripted "i2" "1" [] == misfit "the run makes choice 1, of type i2, and --choices gives 0 choices"
#guard scripted "i2" "1" ["1", "0"] == misfit "the run makes 1 choice, and --choices gives 2"
#guard scripted "i2" "0" ["1"] == misfit "the run makes 0 choices, and --choices gives 1"
#guard scripted "i2" "1" ["2"] == misfit "choice 1, 2, is not a value of type i2"
#guard scripted "i2" "1" ["poison"] == misfit "choice 1, poison, is not a value of type i2"
#guard scripted "i1" "true" ["1"] == misfit "choice 1, 1, is not a value of type i1"
#guard scripted "i2" "1" ["01"] == misfit "choice 1, 01, is not a value of type i2"
#guard scripted "i2" "1" [""] == misfit "choice 1, , is not a value of type i2"

/-- `@f(%a: i64) -> i64`, which freezes `add nsw %a, 1` once, as `%f`, and
returns `sub %f, %f`: every use of `%f` sees the same bits. -/
def subSelf (ty : String) : String :=
  body ("func @f(%a: " ++ ty ++ ") -> " ++ ty)
    ["^e:", "  %m: " ++ ty ++ " = const 1 @0", "  %p: " ++ ty ++ " = add nsw %a, %m @0",
     "  %f: " ++ ty ++ " = freeze %p @0", "  %d: " ++ ty ++ " = sub %f, %f @0", "  ret %d @0"]

#guard runText (subSelf "i64") "@f" ["9223372036854775807"] (mode := .scripted ["5"]) ==
  returns ["0"] 1
#guard runText (subSelf "i64") "@f" ["9223372036854775807"]
  (mode := .scripted ["-9223372036854775808"]) == returns ["0"] 1

/-! # `freeze` in exhaustive mode

Exhaustive mode lists each outcome once, in the order that the paths first
reach it, each choice from zero up as an unsigned number. -/

/-- The report of exhaustive mode: its outcomes, each a JSON object, and
the most choices that one path makes. -/
def outcomes (os : List String) (c : Nat) (status : UInt32 := 0) : RunReport :=
  { out := "{\"kind\":\"outcomes\",\"choices\":" ++ toString c ++ ",\"outcomes\":[" ++
      ",".intercalate os ++ "]}", status }

/-- The JSON object of an outcome that returns `vs`. -/
def ret (vs : List String) : String := "{\"kind\":\"return\",\"values\":" ++ valuesJson vs ++ "}"

/-- What exhaustive mode reports on the text `t`. -/
def explore (t : String) (args : List String) (budget : Nat := defaultChoiceBits)
    (fuel : Nat := defaultFuel) : RunReport :=
  runText t "@f" args fuel (.exhaustive budget)

#guard explore (frozen "i2") ["1"] == outcomes [ret ["0"], ret ["1"], ret ["-2"], ret ["-1"]] 1
#guard explore (frozen "i1") ["true"] == outcomes [ret ["false"], ret ["true"]] 1
#guard explore (frozen "i2") ["0"] == outcomes [ret ["1"]] 0
#guard (explore (frozen "i8") ["127"]).out.startsWith
  ("{\"kind\":\"outcomes\",\"choices\":1,\"outcomes\":[" ++ ret ["0"] ++ "," ++ ret ["1"] ++ ",")
#guard ((explore (frozen "i8") ["127"]).out.splitOn "\"kind\":\"return\"").length == 257
-- `sub %f, %f` is `0` on every path.
#guard explore (subSelf "i8") ["127"] == outcomes [ret ["0"]] 1
-- A run that chooses more bits than the budget gives no set.
#guard explore (subSelf "i64") ["9223372036854775807"] ==
  { out := "{\"kind\":\"choice-budget-exceeded\",\"budget\":16}", status := 0 }
#guard explore (frozen "i2") ["1"] (budget := 1) ==
  { out := "{\"kind\":\"choice-budget-exceeded\",\"budget\":1}", status := 0 }
#guard explore (frozen "i2") ["1"] (budget := 2) == explore (frozen "i2") ["1"]
#guard explore (frozen "i2") ["0"] (budget := 0) == outcomes [ret ["1"]] 0

/-- Two freezes of one poison at `i1`, and the difference of their bits. -/
def twoFreezes : String :=
  body "func @f(%a: i1) -> i1"
    ["^e:", "  %p: i1 = add nsw %a, %a @0", "  %f: i1 = freeze %p @0", "  %g: i1 = freeze %p @0",
     "  %d: i1 = sub %f, %g @0", "  ret %d @0"]

-- Each freeze chooses its own bits, so they may differ.
#guard explore twoFreezes ["true"] == outcomes [ret ["false"], ret ["true"]] 2
#guard explore twoFreezes ["true"] (budget := 1) ==
  { out := "{\"kind\":\"choice-budget-exceeded\",\"budget\":1}", status := 0 }
#guard runText twoFreezes "@f" ["true"] (mode := .scripted ["true", "false"]) == returns ["true"] 2
#guard runText twoFreezes "@f" ["true"] (mode := .scripted ["true"]) ==
  misfit "the run makes choice 2, of type i1, and --choices gives 1 choice"
-- Fuel runs out before the choice on every path.
#guard explore (frozen "i2") ["1"] (fuel := 2) == outcomes ["{\"kind\":\"fuel-exhausted\"}"] 0
#guard explore (frozen "i2") ["1"] (fuel := 3) == outcomes ["{\"kind\":\"fuel-exhausted\"}"] 1
-- A stuck path is listed, and makes the exit status 1.
#guard explore (body "func @f(%a: i1) -> i1"
    ["^e:", "  %p: i1 = add nsw %a, %a @0", "  %f: i1 = freeze %p @0"]) ["true"] ==
  outcomes ["{\"kind\":\"stuck\",\"reason\":\"a block ends without a terminator\"}"] 1 1
-- An op without rules after a choice is an error, in either mode.
#guard explore (body "func @f(%a: i1) -> i1"
    ["^e:", "  %p: i1 = add nsw %a, %a @0", "  %f: i1 = freeze %p @0",
     "  %g: i1 = icmp eq %f, %f @0", "  ret %g @0"]) ["true"] ==
  fails 2 "fir-ref: @f: icmp eq has no execution rules yet"
-- The budget is checked first: past it, a path that would reach an op
-- without rules is not run.
/-- `@f(%a: i64) -> i1`, which freezes `add nsw %a, 1` and returns
`icmp eq %f, %f`. -/
def icmpSelf : String :=
  body "func @f(%a: i64) -> i1"
    ["^e:", "  %m: i64 = const 1 @0", "  %p: i64 = add nsw %a, %m @0", "  %f: i64 = freeze %p @0",
     "  %d: i1 = icmp eq %f, %f @0", "  ret %d @0"]

#guard explore icmpSelf ["9223372036854775807"] ==
  { out := "{\"kind\":\"choice-budget-exceeded\",\"budget\":16}", status := 0 }
#guard runText icmpSelf "@f" ["9223372036854775807"] (mode := .scripted ["5"]) ==
  fails 2 "fir-ref: @f: icmp eq has no execution rules yet"

/-! # UB in exhaustive mode

With the test semantics `addIsUB`, every path hits UB after its choice,
and exhaustive mode lists the one outcome. -/

/-- What exhaustive mode would report on the first function of the text
`t` with the semantics `s`. -/
def exploreIn (s : DialectDenote CoreDialect Tree) (t : String) (args : List String) :
    Option RunReport :=
  match parseCore t with
  | .error _ => none
  | .ok m => m.funcs.head?.bind fun f =>
    match testArgs (f.params.map (·.2)) args with
    | .error _ => none
    | .ok vs => letI := s
      some (exhaustiveReport "@f" 16 ((f.run (m := Tree) vs defaultFuel).run.explore 16))

#guard exploreIn addIsUB (body "func @f(%a: i1) -> i1"
    ["^e:", "  %t: i1 = const true @0", "  %p: i1 = sub nsw %a, %t @0", "  %f: i1 = freeze %p @0",
     "  %g: i1 = add %f, %f @0", "  ret %g @0"]) ["false"] ==
  some (outcomes ["{\"kind\":\"ub\",\"reason\":\"add is \\\"UB\\\"\\nhere\"}"] 1)

/-! # The theorems' axioms -/

/-- info: 'Fir.Core.exhaustive_outcomes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.exhaustive_outcomes

/-- info: 'Fir.Core.exhaustive_stuck' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.exhaustive_stuck

/-- info: 'Fir.Core.scripted_outcomes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.scripted_outcomes

/-- info: 'Fir.Core.scripted_stuck' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.scripted_stuck

/-- info: 'Fir.ChoiceTree.explore_isSome_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.ChoiceTree.explore_isSome_iff

/-- info: 'Fir.Core.sub_propagatesPoison' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.sub_propagatesPoison

/-- info: 'Fir.Core.sub_returnsOnDefined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.sub_returnsOnDefined

/-- info: 'Fir.Core.sub_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.sub_total

/-- info: 'Fir.Core.sub_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.sub_monotone

/-- info: 'Fir.Core.mul_propagatesPoison' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.mul_propagatesPoison

/-- info: 'Fir.Core.mul_returnsOnDefined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.mul_returnsOnDefined

/-- info: 'Fir.Core.mul_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.mul_total

/-- info: 'Fir.Core.mul_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.mul_monotone

/-- info: 'Fir.Core.freeze_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.freeze_total

/-- info: 'Fir.Core.freeze_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.freeze_monotone

end FirTest
