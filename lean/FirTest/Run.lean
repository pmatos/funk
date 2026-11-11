import FirTest.Parse
import FirRef.RunArgs

/-!
Tests of the interpreter and of `fir-ref run` (ADR-2026-10-30-1856), on
`FirRef.runBytes`, which computes what `fir-ref run` writes and its exit
status: each kind of result, the widths 1, 7, 8, 33, 64, 128 and 16777215,
several results and none, fuel, each stuck case that a text reaches, calls
without end, `poison` arguments (#123), and argument errors, among them a
comment of a million characters (#135), with the axioms of
`argAttr_eq_argAttrP`, which reads an argument over positions. Most of these
runs make no choice, in scripted mode with no choices, the default;
`FirTest.Modes` tests the modes on runs that choose.

`FirTest.Interpreter` tests the interpreter's paths that these ops do not
reach, and `scripts/check-fir-ref.sh test` runs the built `fir-ref` on the
shared corpus.
-/

namespace FirTest

open Fir FirRef

/-- What `fir-ref run` reports on the text `t`. -/
def runText (t func : String) (args : List String := []) (fuel : Nat := defaultFuel)
    (mode : Mode := .scripted []) : RunReport :=
  runBytes "t.fir" t.toUTF8 fuel func args mode

/-- The JSON of a list of values. -/
def valuesJson (vs : List String) : String := "[" ++ ",".intercalate (vs.map ("\"" ++ · ++ "\"")) ++ "]"

/-- The report of a run that returns `vs` after `c` choices. -/
def returns (vs : List String) (c : Nat := 0) : RunReport :=
  { out := "{\"kind\":\"return\",\"values\":" ++ valuesJson vs ++ ",\"choices\":" ++ toString c ++ "}",
    status := 0 }

/-- The report of a stuck run. -/
def stuckBy (reason : String) : RunReport :=
  { out := "{\"kind\":\"stuck\",\"reason\":\"" ++ reason ++ "\",\"choices\":0}", status := 1 }

/-- The report of a run that runs out of fuel. -/
def exhausted : RunReport := { out := "{\"kind\":\"fuel-exhausted\",\"choices\":0}", status := 0 }

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

/-! # Fuel

Each op takes a step, `ret` included: `@seven` runs two ops. -/

#guard runText seven "@seven" (fuel := 0) == exhausted
#guard runText seven "@seven" (fuel := 1) == exhausted
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
  stuckBy "an op owns a region of the core's kind, and no rule runs one"
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

/-! # Calls without end

A function that calls itself without end runs out of fuel, in either mode:
each call takes a step, and its callee runs on the steps that are left
(#20). Before #20 gave `call` its meaning, `fir-ref` reported these runs
as an error, an op without rules (ADR-2026-10-30-1855); no core op is
without rules now. `FirTest.Calls` tests calls that return. -/

#guard runText (body "func @f(%a: i8) -> i8" ["^e:", "  %s: i8 = call @f %a @0", "  ret %s @0"])
    "@f" ["1"] (fuel := 100) == exhausted
#guard runText (body "func @f(%a: i8) -> i1" ["^e:", "  %s: i1 = call @f %a @0", "  ret %s @0"])
    "@f" ["1"] (fuel := 100) (mode := .exhaustive 16) ==
  { out := "{\"kind\":\"outcomes\",\"choices\":0,\"outcomes\":[{\"kind\":\"fuel-exhausted\"}]}",
    status := 0 }
#guard runText (body "func @f()" ["^e:", "  call @f @0", "  ret @0"]) "@f" (fuel := 100) == exhausted

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
#guard ["ptr(0, 0)", "ptr(none, 0)", "null", "0x0"].all fun a =>
  runText (body "func @p(%x: ptr(1))" ["^e:", "  ret @0"]) "@p" [a] ==
    fails 2 ("fir-ref: " ++ shown a ++ " is not a value of type ptr(1)")
-- An argument is lexed over positions, so a comment of a million characters
-- is no value, alone or after one (#135).
#guard ["//", "// one", "1 2", "-", "//\x01", "// " ++ "".pushn 'x' 1000000,
    "1 // " ++ "".pushn 'x' 1000000].all
  fun a => addI8 a == fails 2 ("fir-ref: " ++ shown a ++ " is not a value of type i8")

/--
info: 'FirRef.argAttr_eq_argAttrP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms FirRef.argAttr_eq_argAttrP

/-! # Poison arguments

`poison` is an argument of any `iN`, spelled as the output spells a poison
value (#123), and a run on it is the spec's run on a poison argument. It is
an argument of a pointer type too, the only one, since a run starts with no
allocation. It is no choice: `freeze` chooses a value. -/

#guard addI8 "poison" == returns ["poison"]
#guard runText (addAt "i1") "@f" ["true", "poison"] == returns ["poison"]
#guard runText (addAt "i16777215") "@f" ["poison", "1"] == returns ["poison"]
#guard runText (addAt "i128") "@f" ["poison", "poison"] == returns ["poison"]
#guard runText results "@swap" ["poison", "-2"] == returns ["-2", "poison"]
#guard runText results "@three" ["poison"] == returns ["poison", "-5", "poison"]
-- Only `poison`, spelled exactly so.
#guard ["Poison", "POISON", " poison", "poison ", "\"poison\"", "%poison", "poison()"].all
  fun a => addI8 a == fails 2 ("fir-ref: " ++ a ++ " is not a value of type i8")
#guard runText (body "func @p(%x: ptr)" ["^e:", "  ret @0"]) "@p" ["poison"] == returns []
#guard runText (body "func @p(%a: i8, %x: ptr(7)) -> ptr(7), i8" ["^e:", "  ret %x, %a @0"]) "@p"
  ["poison", "poison"] == returns ["poison", "poison"]
-- A pointer is written by its allocation and offset, which no run of this
-- stage gives, since no op makes a pointer yet.
#guard valueText ⟨.ptr 0, (.value ⟨some 3, -4⟩ : PoisonOr Memory.Pointer)⟩ == "ptr(3, -4)"
#guard valueText ⟨.ptr 2, (.value ⟨none, 0⟩ : PoisonOr Memory.Pointer)⟩ == "ptr(none, 0)"
-- A pointer passes through a block argument and a call as it is.
#guard runText ("func @id(%x: ptr) -> ptr {\n^e:\n  ret %x @0\n}\n\n" ++ body "func @p(%x: ptr) -> ptr"
    ["^e:", "  br ^b(%x) @0", "^b(%y: ptr):", "  %z: ptr = call @id %y @0", "  ret %z @0"])
    "@p" ["poison"] == returns ["poison"]

/-- `@f(%a: i2) -> i2`, which returns `freeze %a`. -/
def freezeArg : String := body "func @f(%a: i2) -> i2" ["^e:", "  %f: i2 = freeze %a @0", "  ret %f @0"]

-- A poison argument that reaches `freeze` makes a choice, in each mode.
#guard runText freezeArg "@f" ["1"] == returns ["1"]
#guard runText freezeArg "@f" ["poison"] (mode := .scripted ["-2"]) == returns ["-2"] 1
#guard runText freezeArg "@f" ["poison"] (mode := .exhaustive 16) ==
  { out := "{\"kind\":\"outcomes\",\"choices\":1,\"outcomes\":[" ++
      ",".intercalate (["0", "1", "-2", "-1"].map fun v =>
        "{\"kind\":\"return\",\"values\":[\"" ++ v ++ "\"]}") ++ "]}",
    status := 0 }
#guard (runText freezeArg "@f" ["poison"] (mode := .sampled 0)).status == 0
#guard runText freezeArg "@f" ["poison"] == fails 2
  "fir-ref: @f: the choices do not fit the run: the run makes choice 1, of type i2, and --choices gives 0 choices"
#guard runText freezeArg "@f" ["poison"] (mode := .scripted ["poison"]) == fails 2
  "fir-ref: @f: the choices do not fit the run: choice 1, poison, is not a value of type i2"
-- A branch on a poison argument is UB, and a callee gets it as poison.
#guard runText (body "func @f(%c: i1) -> i1"
    ["^e:", "  cond_br %c, ^t, ^t @0", "^t:", "  ret %c @0"]) "@f" ["poison"] ==
  { out := "{\"kind\":\"ub\",\"reason\":\"cond_br on poison\",\"choices\":0}", status := 0 }
#guard runText (oneFunc ("func @f(%a: i8) -> i8 {\n^e:\n  %r: i8 = call @g %a @0\n  ret %r @0\n}\n\n" ++
    "func @g(%b: i8) -> i8 {\n^e:\n  ret %b @0\n}\n")) "@f" ["poison"] == returns ["poison"]
#guard (runText "func @f() {\n" "@f").out == "" && (runText "func @f() {\n" "@f").status == 1 &&
  (runText "func @f() {\n" "@f").err.startsWith "t.fir:2:1: parse error: "

/-! # The command line of `run` -/

/-- The mode that `run`'s command line gives, in words. -/
def modeText : Mode → String
  | .scripted cs => s!"scripted {cs}"
  | .exhaustive b => s!"exhaustive {b}"
  | .sampled s => s!"sampled {s}"

/-- The fuel, file, function and arguments that `run`'s command line gives,
or its error. -/
def runLine (args : List String) : String :=
  match runArgs args with
  | .ok a => s!"{a.fuel} {a.file} {a.func} {a.args}"
  | .error why => "error: " ++ why

/-- The mode that `run`'s command line gives, or its error. -/
def modeLine (args : List String) : String :=
  match runArgs args with
  | .ok a => modeText a.mode
  | .error why => "error: " ++ why

#guard runLine ["f.fir", "@f", "-5", "true"] == "1000000 f.fir @f [-5, true]"
#guard runLine ["--fuel", "7", "-", "@f"] == "7 - @f []"
#guard runLine ["f.fir", "--fuel", "7", "@f", "1"] == "7 f.fir @f [1]"
#guard runLine ["--", "--fuel", "@f"] == "1000000 --fuel @f []"
#guard runLine ["f.fir", "@f", "--", "--fuel", "7"] == "1000000 f.fir @f [--fuel, 7]"
#guard runLine ["--fuel", "x", "f.fir", "@f"] == "error: --fuel takes a number of steps, not x"
-- N is ASCII decimal digits: no `_` separators, sign or space.
#guard ["1_0", "+1", "-1", " 1", ""].all fun n =>
  runLine ["--fuel", n, "f.fir", "@f"] == "error: --fuel takes a number of steps, not " ++ n
#guard runLine ["--fuel", "010", "f.fir", "@f"] == "10 f.fir @f []"
#guard runLine ["f.fir", "@f", "--fuel"] == "error: --fuel takes a number of steps"
#guard runLine ["--check", "f.fir", "@f"] == "error: unknown option --check"
#guard runLine [] == "error: no FILE given; use - for standard input"
#guard runLine ["f.fir"] == "error: no @FUNC given"
-- Scripted mode, with no choices, is the default.
#guard modeLine ["f.fir", "@f"] == "scripted []"
#guard modeLine ["--choices", "1,-2,true", "f.fir", "@f"] == "scripted [1, -2, true]"
#guard modeLine ["--choices", "", "f.fir", "@f"] == "scripted []"
#guard modeLine ["--choices", "-1", "f.fir", "@f", "-1"] == "scripted [-1]"
#guard modeLine ["--choices", "1,,2", "f.fir", "@f"] == "scripted [1, , 2]"
#guard modeLine ["--choices", "1", "--choices", "2", "f.fir", "@f"] == "scripted [2]"
#guard modeLine ["f.fir", "@f", "--", "--choices", "1"] == "scripted []"
#guard modeLine ["--exhaustive", "f.fir", "@f"] == "exhaustive 16"
#guard modeLine ["--choice-bits", "3", "--exhaustive", "f.fir", "@f"] == "exhaustive 3"
#guard modeLine ["--exhaustive", "--choices", "1", "f.fir", "@f"] ==
  "error: --choices does not go with --exhaustive"
#guard modeLine ["--choice-bits", "3", "f.fir", "@f"] == "error: --choice-bits needs --exhaustive"
#guard modeLine ["--exhaustive", "--choice-bits", "x", "f.fir", "@f"] ==
  "error: --choice-bits takes a number of bits, not x"
#guard modeLine ["f.fir", "@f", "--choice-bits"] == "error: --choice-bits takes a number of bits"
#guard modeLine ["f.fir", "@f", "--choices"] == "error: --choices takes a list of choices"

end FirTest
