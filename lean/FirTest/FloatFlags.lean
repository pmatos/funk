import FirTest.FloatArith
import FirTest.ValidateOps

/-!
Tests of #242's fast-math flags on `FirRef.runBytes`, which computes what
`fir-ref run` writes, and on the validation check (ADR-2026-11-09-1549):
`nnan` and `ninf` make a NaN or an infinite operand or result poison,
with no choice made; `nsz` makes a zero result either zero; and
`contract` and `reassoc` read, and validation rejects them.
-/

namespace FirTest

open Fir FirRef

/-- What scripted mode reports on `op` with the flags `fl`, a word list
with a space before each, at `ty` on `args`, with `cs`. -/
def flagged (op fl ty : String) (args : List String) (cs : List String := []) : RunReport :=
  let attr := if ["fneg", "fabs", "frem", "fmod"].contains op then fl else fl ++ " round(rne)"
  runText (floatOp op attr ty args.length) "@f" args (mode := .scripted cs)

/-- `@f` that compares two `ty` with `fcmp`, its flags `fl` and the
predicate `p`. -/
def fcmpOp (fl p ty : String) : String :=
  body ("func @f(%a: " ++ ty ++ ", %b: " ++ ty ++ ") -> i1")
    ["^e:", "  %r: i1 = fcmp" ++ fl ++ " " ++ p ++ " %a, %b @0", "  ret %r @0"]

/-! # `nnan` -/

-- A NaN operand gives poison, and so does a NaN result, which then makes
-- no choice: without the flag it needs one.
#guard flagged "fadd" " nnan" "f32" ["0x7fc00000", "1.0"] == returns ["poison"]
#guard flagged "fsub" " nnan" "f32" ["0x7f800000", "0x7f800000"] == returns ["poison"]
#guard flagged "sqrt" " nnan" "f64" ["-1.0"] == returns ["poison"]
#guard flagged "fneg" " nnan" "f16" ["0x7e00"] == returns ["poison"]
-- Other results are the op's own.
#guard flagged "fadd" " nnan" "f32" ["1.0", "2.0"] == returns ["3.0"]
#guard flagged "fdiv" " nnan" "bf16" ["1.0", "0.0"] == returns ["0x7f80"]

-- The remainders carry the flags too: a zero divisor gives a NaN, so
-- poison under `nnan`.
#guard flagged "frem" " nnan" "f32" ["1.0", "0.0"] == returns ["poison"]
#guard flagged "fmod" " nnan" "f64" ["3.0", "2.0"] == returns ["1.0"]

/-! # `ninf` -/

-- An infinite operand gives poison, even when the result is finite.
#guard flagged "fdiv" " ninf" "f32" ["1.0", "0x7f800000"] == returns ["poison"]
#guard flagged "fabs" " ninf" "f64" ["0xfff0000000000000"] == returns ["poison"]
-- A result that rounds to an infinity gives poison.
#guard flagged "fmul" " ninf" "f16" ["65500.0", "2.0"] == returns ["poison"]
#guard flagged "fdiv" " ninf" "bf16" ["1.0", "-0.0"] == returns ["poison"]
-- A NaN result without `nnan` is still any NaN.
#guard flagged "fdiv" " ninf" "f32" ["0.0", "0.0"] ["0"] == returns ["0x7fc00000"] 1
#guard flagged "fma" " ninf" "f32" ["1.0", "1.0", "1.0"] == returns ["2.0"]

-- An infinite divisor gives poison, where the remainder is the dividend
-- without the flag.
#guard flagged "frem" " ninf" "f32" ["1.0", "0x7f800000"] == returns ["poison"]
#guard flagged "fmod" "" "f32" ["1.0", "0x7f800000"] == returns ["1.0"]

/-! # `nsz` -/

-- A zero result has either sign: the choice is one bit.
#guard explore (floatOp "fsub" " nsz round(rne)" "f32" 2) ["1.0", "1.0"] ==
  outcomes [ret ["0.0"], ret ["-0.0"]] 1
#guard explore (floatOp "fneg" " nsz" "f64" 1) ["0.0"] == outcomes [ret ["-0.0"], ret ["0.0"]] 1
-- Every other result is one value, with no choice.
#guard flagged "fadd" " nsz" "f32" ["1.0", "2.0"] == returns ["3.0"]
#guard explore (floatOp "fadd" " nsz round(rne)" "f32" 2) ["1.0", "2.0"] == outcomes [ret ["3.0"]] 0

/-! # All three, and `fcmp` -/

#guard flagged "fma" " nnan ninf nsz" "f128" ["1.0", "0x7fff0000000000000000000000000000", "1.0"] ==
  returns ["poison"]
#guard explore (fcmpOp " nnan" "uno" "f32") ["0x7fc00000", "1.0"] == outcomes [ret ["poison"]] 0
#guard explore (fcmpOp " ninf" "olt" "f32") ["1.0", "0x7f800000"] == outcomes [ret ["poison"]] 0
#guard explore (fcmpOp " nnan ninf nsz" "oeq" "f32") ["-0.0", "0.0"] == outcomes [ret ["true"]] 0
#guard explore (fcmpOp " nsz" "uno" "f32") ["0x7fc00000", "1.0"] == outcomes [ret ["true"]] 0

/-! # How the flags are written

The flags come first, in the order `nnan`, `ninf`, `nsz`, `contract`,
`reassoc`, each at most once. -/

#guard [(" nsz nnan", "fadd"), (" nnan nnan", "fadd"), (" round(rne) nnan", "fneg"),
  (" ninf", "fbad")].all fun (fl, op) =>
    (runText (floatOp op fl "f32" 2) "@f" ["1.0", "1.0"]).status == 1
#guard (runText (body "func @f(%a: f32, %b: f32) -> f32"
  ["^e:", "  %r: f32 = fadd round(rne) nnan %a, %b @0", "  ret %r @0"]) "@f" ["1.0", "1.0"]).status == 1

/-! # Decoding the flags

`Op.decode` reads the flags first, in their order, and then the op's own
attributes. -/

open Fir.Core in
#guard Op.decode "fcmp" [.word "nnan", .word "olt"] [.float 8 23, .float 8 23] [.int 1] ==
  some (.fcmp .olt { nnan := true } 8 23)
open Fir.Core in
#guard Op.decode "fcmp" [.word "olt", .word "nnan"] [.float 8 23, .float 8 23] [.int 1] == none
open Fir.Core in
#guard Op.decode "fadd" [.word "ninf", .word "nsz", roundAttr] [.float 8 23, .float 8 23]
  [.float 8 23] == some (.fbin .fadd { ninf := true, nsz := true } 8 23)
open Fir.Core in
#guard Op.decode "fadd" [roundAttr, .word "nnan"] [.float 8 23, .float 8 23] [.float 8 23] == none
open Fir.Core in
#guard Op.decode "fneg" [.word "nnan"] [.float 8 23] [.float 8 23] ==
  some (.funary .fneg { nnan := true } 8 23)
open Fir.Core in
#guard Op.decode "fneg" [.word "reassoc", .word "contract"] [.float 8 23] [.float 8 23] == none

/-! # The reserved words

`contract` and `reassoc` read, and validation rejects every float op that
carries either. -/

/-- A module of one function `@f(%a: f32, %b: f32)` whose entry holds `op`. -/
def onFloats (op : String) : String :=
  oneFunc ("func @f(%a: f32, %b: f32) {\n^entry:\n  " ++ op ++ "\n  ret @0\n}\n")

#guard checks (onFloats "%r: f32 = fadd contract round(rne) %a, %b @0")
  ["the op breaks its dialect's own rule"]
#guard checks (onFloats "%r: f32 = fneg nnan reassoc %a @0") ["the op breaks its dialect's own rule"]
#guard checks (onFloats "%r: i1 = fcmp contract reassoc olt %a, %b @0")
  ["the op breaks its dialect's own rule"]
#guard checks (onFloats "%r: f32 = fma nnan ninf nsz round(rne) %a, %b, %a @0") []

end FirTest
