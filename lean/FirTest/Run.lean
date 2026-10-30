import FirTest.Parse
import FirRef.Run

/-!
Tests of the interpreter and of `fir-ref run` (ADR-2026-10-30-1856), on
`FirRef.runBytes`, which computes what `fir-ref run` writes and its exit
status: each kind of result, the widths 1, 7, 8, 33, 64, 128 and 16777215,
several results and none, poison arguments, fuel, each stuck case that a
text reaches, ops without rules (ADR-2026-10-30-1855), and argument errors.

`FirTest.Interpreter` tests the interpreter's paths that these ops do not
reach, and `scripts/check-fir-ref.sh test` runs the built `fir-ref` on the
shared corpus.
-/

namespace FirTest

open Fir FirRef

/-- What `fir-ref run` reports on the text `t`. -/
def runText (t func : String) (args : List String := []) (fuel : Nat := defaultFuel) : RunReport :=
  runBytes "t.fir" t.toUTF8 fuel func args

/-- The report of a run that returns `vs`. -/
def returns (vs : List String) : RunReport :=
  { out := "{\"kind\":\"return\",\"values\":[" ++ ",".intercalate (vs.map ("\"" ++ · ++ "\"")) ++ "]}",
    status := 0 }

/-- The report of a stuck run. -/
def stuckBy (reason : String) : RunReport :=
  { out := "{\"kind\":\"stuck\",\"reason\":\"" ++ reason ++ "\"}", status := 1 }

/-- A report on standard error only. -/
def fails (status : UInt32) (err : String) : RunReport := { err, status }

/-- `@f(%a: T, %b: T) -> T`, which returns `add %a, %b`. -/
def addAt (ty : String) : String :=
  oneFunc ("func @f(%a: " ++ ty ++ ", %b: " ++ ty ++ ") -> " ++ ty ++ " {\n^e:\n  %s: " ++ ty ++
    " = add %a, %b @0\n  ret %s @0\n}\n")

/-! # Values, at every width -/

#guard runText seven "@seven" == returns ["7"]
#guard runText (addAt "i1") "@f" ["true", "true"] == returns ["false"]
#guard runText (addAt "i1") "@f" ["false", "true"] == returns ["true"]
#guard runText (addAt "i7") "@f" ["63", "1"] == returns ["-64"]
#guard runText (addAt "i8") "@f" ["127", "1"] == returns ["-128"]
#guard runText (addAt "i8") "@f" ["-128", "-1"] == returns ["127"]
#guard runText (addAt "i33") "@f" ["4294967295", "1"] == returns ["-4294967296"]
#guard runText (addAt "i64") "@f" ["9223372036854775807", "1"] == returns ["-9223372036854775808"]
#guard runText (addAt "i128") "@f" ["170141183460469231731687303715884105727", "2"] ==
  returns ["-170141183460469231731687303715884105727"]
#guard runText (addAt "i16777215") "@f" ["-1", "-1"] == returns ["-2"]
#guard runText (addAt "i16777215") "@f" ["1", "-1"] == returns ["0"]

/-! # Several results, and none -/

/-- Functions with no result, one, and several. -/
def results : String := oneFunc
  "func @none() {\n^e:\n  ret @0\n}\n\nfunc @swap(%a: i8, %b: i16) -> i16, i8 {\n^e:\n  ret %b, %a @0\n}\n\nfunc @three(%a: i1) -> i1, i64, i1 {\n^e:\n  %c: i64 = const -5 @0\n  ret %a, %c, %a @0\n}\n"

#guard runText results "@none" == returns []
#guard runText results "@swap" ["1", "-2"] == returns ["-2", "1"]
#guard runText results "@three" ["true"] == returns ["true", "-5", "true"]

/-! # Poison

A poison argument is passed on as it is, and `add` gives poison when either
operand is poison. -/

#guard runText (addAt "i8") "@f" ["poison", "1"] == returns ["poison"]
#guard runText (addAt "i1") "@f" ["true", "poison"] == returns ["poison"]
#guard runText (addAt "i16777215") "@f" ["poison", "poison"] == returns ["poison"]
#guard runText results "@swap" ["poison", "3"] == returns ["3", "poison"]

/-! # Fuel

Each op takes a step, `ret` included: `@seven` runs two ops. -/

#guard runText seven "@seven" (fuel := 0) == { out := "{\"kind\":\"fuel-exhausted\"}", status := 0 }
#guard runText seven "@seven" (fuel := 1) == { out := "{\"kind\":\"fuel-exhausted\"}", status := 0 }
#guard runText seven "@seven" (fuel := 2) == returns ["7"]

/-! # Stuck

Texts that parse but that validation rejects, run up to the case it rules
out. -/

/-- One function `@f`, with a body of lines, and the location table. -/
def body (header : String) (lines : List String) : String :=
  oneFunc (header ++ " {\n" ++ String.join (lines.map (· ++ "\n")) ++ "}\n")

#guard runText (body "func @f()" []) "@f" == stuckBy "the function has no blocks"
#guard runText (body "func @f() -> i32" ["^e:", "  %c: i32 = const 1 @0"]) "@f" ==
  stuckBy "a block ends without a terminator"
#guard runText (body "func @f() -> i32"
    ["^e:", "  %b: i32 = add %a, %a @0", "  %a: i32 = const 1 @0", "  ret %b @0"]) "@f" ==
  stuckBy "%a is not defined"
#guard runText (body "func @f()" ["^e:", "  ret {", "  ^b:", "    ret @0", "  } @0"]) "@f" ==
  stuckBy "an op owns a region, and no rule runs one"
-- A function returns values of its result types, and no op follows a
-- terminator.
#guard runText (body "func @f() -> i32" ["^e:", "  %c: i8 = const 1 @0", "  ret %c @0"]) "@f" ==
  stuckBy "the function returns values of types other than its result types"
#guard runText (body "func @f() -> i32" ["^e:", "  ret @0"]) "@f" ==
  stuckBy "the function returns values of types other than its result types"
#guard runText (body "func @f()" ["^e:", "  %c: i8 = const 1 @0", "  ret %c @0"]) "@f" ==
  stuckBy "the function returns values of types other than its result types"
#guard runText (body "func @f() -> i8" ["^e:", "  %c: i8 = const 1 @0", "  ret %c @0", "  ret %c @0"])
  "@f" == stuckBy "an op follows the terminator of its block"
#guard runText (body "func @f() -> i8"
    ["^e:", "  %c: i8 = const 1 @0", "  ret %c @0", "  %d: i8 = const 2 @0"]) "@f" ==
  stuckBy "an op follows the terminator of its block"
-- The entry block's arguments are the function's parameters.
#guard runText (body "func @f(%x: i8) -> i8" ["^e(%y: i8):", "  ret %x @0"]) "@f" ["1"] ==
  stuckBy "the entry block ^e declares arguments"
-- The run stops at the first stuck op: what follows is not run.
#guard runText (body "func @f() -> i32"
    ["^e:", "  %b: i32 = add %a, %a @0", "  %a: i32 = sub %b, %b @0", "  ret %b @0"]) "@f" ==
  stuckBy "%a is not defined"

/-! # Ops without rules

Every core op but `const`, `add` without flags and `ret` has no rules yet,
so `fir-ref` reports an error and no result (ADR-2026-10-30-1855). -/

#guard runText (body "func @f(%a: i8) -> i8" ["^e:", "  %s: i8 = sub %a, %a @0", "  ret %s @0"])
    "@f" ["1"] == fails 2 "fir-ref: @f: sub has no execution rules yet"
#guard runText (body "func @f(%a: i8) -> i8" ["^e:", "  %s: i8 = add nsw %a, %a @0", "  ret %s @0"])
    "@f" ["1"] == fails 2 "fir-ref: @f: add nsw has no execution rules yet"
#guard runText (body "func @f()" ["^e:", "  br ^n @0", "^n:", "  ret @0"]) "@f" ==
  fails 2 "fir-ref: @f: br has no execution rules yet"

/-! # Arguments -/

#guard runText (addAt "i8") "@f" ["1"] == fails 2 "fir-ref: @f takes 2 arguments, not 1"
#guard runText results "@three" [] == fails 2 "fir-ref: @three takes 1 argument, not 0"
#guard runText seven "@seven" ["1"] == fails 2 "fir-ref: @seven takes 0 arguments, not 1"
#guard runText seven "@g" == fails 2 "fir-ref: t.fir has no function @g"
-- The function is named as text writes it: `@"seven"` is written `@seven`.
#guard runText seven "@\"seven\"" == fails 2 "fir-ref: t.fir has no function @\"seven\""
#guard runText seven "seven" == fails 2 "fir-ref: t.fir has no function seven"
#guard runText (quoted "a b") "@\"a b\"" == returns []
#guard runText (quoted "\\n") "@\"\\n\"" == returns []

/-- `addAt "i8"` on `1` and `a`. -/
def addI8 (a : String) : RunReport := runText (addAt "i8") "@f" ["1", a]

-- Signed decimal in the type's range, spelled as `const` is in text.
#guard addI8 "-128" == returns ["-127"]
#guard ["128", "-129", "+1", "01", "-0", " 1", "1 ", "1.0", "0x1", "", "true", "1 // one"].all
  fun a => addI8 a == fails 2 ("fir-ref: " ++ a ++ " is not a value of type i8")
#guard addI8 "1\n" == fails 2 "fir-ref: 1\\x0a is not a value of type i8"
#guard addI8 "\x7f" == fails 2 "fir-ref: \\x7f is not a value of type i8"
-- `true` and `false` at `i1`, and no number.
#guard ["1", "0", "-1", "TRUE"].all fun a =>
  runText (addAt "i1") "@f" ["true", a] == fails 2 ("fir-ref: " ++ a ++ " is not a value of type i1")
#guard runText (body "func @p(%x: ptr)" ["^e:", "  ret @0"]) "@p" ["0"] ==
  fails 2 "fir-ref: 0 is not a value of type ptr"
#guard (runText "func @f() {\n" "@f").out == "" && (runText "func @f() {\n" "@f").status == 1 &&
  (runText "func @f() {\n" "@f").err.startsWith "t.fir:2:1: parse error: "

/-! # The command line of `run` -/

/-- The fuel, file, function and arguments that `run`'s command line gives,
or its error. -/
def runLine (args : List String) : String :=
  match runArgs args with
  | .ok a => s!"{a.fuel} {a.file} {a.func} {a.args}"
  | .error why => "error: " ++ why

#guard runLine ["f.fir", "@f", "-5", "true"] == "1000000 f.fir @f [-5, true]"
#guard runLine ["--fuel", "7", "-", "@f"] == "7 - @f []"
#guard runLine ["f.fir", "--fuel", "7", "@f", "1"] == "7 f.fir @f [1]"
#guard runLine ["--", "--fuel", "@f"] == "1000000 --fuel @f []"
#guard runLine ["f.fir", "@f", "--", "--fuel", "7"] == "1000000 f.fir @f [--fuel, 7]"
#guard runLine ["--fuel", "x", "f.fir", "@f"] == "error: --fuel takes a number of steps, not x"
#guard runLine ["f.fir", "@f", "--fuel"] == "error: --fuel takes a number of steps"
#guard runLine ["--check", "f.fir", "@f"] == "error: unknown option --check"
#guard runLine [] == "error: no FILE given; use - for standard input"
#guard runLine ["f.fir"] == "error: no @FUNC given"

end FirTest
