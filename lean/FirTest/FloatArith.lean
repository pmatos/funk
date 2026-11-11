import FirTest.Modes

/-!
Tests of #229's float arithmetic on `FirRef.runBytes`, which computes what
`fir-ref run` writes (ADR-2026-11-11-1800, ADR-2026-11-11-1801). Each op
runs on its hard inputs in the corpus, `float-binary-T` and
`float-unary-fma-T`, against `scripts/harness/float_ref.py`; these check
what the corpus does not: that a result which is not a NaN takes no
choice, that a NaN result is the NaN its choice names, in scripted and in
exhaustive mode, and that `round(rne)` is the one attribute of an op that
rounds.
-/

namespace FirTest

open Fir FirRef

/-- `@f` with operands of type `ty`, which returns `OP %a, ...` with the
attributes `attr`. -/
def floatOp (op attr ty : String) (n : Nat) : String :=
  let names := (["a", "b", "c"].take n).map ("%" ++ ·)
  let params := ", ".intercalate (names.map (· ++ ": " ++ ty))
  body ("func @f(" ++ params ++ ") -> " ++ ty)
    ["^e:", "  %r: " ++ ty ++ " = " ++ op ++ attr ++ " " ++ ", ".intercalate names ++ " @0",
     "  ret %r @0"]

/-- What scripted mode reports on `op` at `ty` on `args`, with `cs`. -/
def farith (op ty : String) (args : List String) (cs : List String := []) : RunReport :=
  let attr := if op == "fneg" || op == "fabs" then "" else " round(rne)"
  runText (floatOp op attr ty args.length) "@f" args (mode := .scripted cs)

-- A result that is not a NaN is one value, with no choice, at every format.
#guard farith "fadd" "f32" ["1.0", "2.0"] == returns ["3.0"]
#guard farith "fsub" "f64" ["0.0", "0.0"] == returns ["0.0"]
#guard farith "fsub" "f64" ["-0.0", "0.0"] == returns ["-0.0"]
#guard farith "fmul" "f16" ["65500.0", "2.0"] == returns ["0x7c00"]
#guard farith "fdiv" "bf16" ["1.0", "0.0"] == returns ["0x7f80"]
#guard farith "fdiv" "bf16" ["1.0", "-0.0"] == returns ["0xff80"]
#guard farith "sqrt" "f128" ["4.0"] == returns ["2.0"]
#guard farith "fneg" "f32" ["0.0"] == returns ["-0.0"]
#guard farith "fabs" "f64" ["-1.5"] == returns ["1.5"]
#guard farith "fma" "f32" ["1.0", "1.0", "1.0"] == returns ["2.0"]
-- A tie goes to the even neighbour: `1 + 2^-24` at `f32` is `1`.
#guard farith "fadd" "f32" ["1.0", "5.9604645e-8"] == returns ["1.0"]
-- A poison operand gives poison, with no choice.
#guard farith "fadd" "f32" ["poison", "1.0"] == returns ["poison"]
#guard farith "fma" "f64" ["1.0", "1.0", "poison"] == returns ["poison"]

/-! # NaN results

A NaN result chooses `m + 1` bits, as `i(m+1)`: its sign, the top bit, and
its mantissa, the low `m`, with a zero mantissa standing for the quiet
NaN. -/

-- `inf - inf` at `f32`: the choice `0` is the quiet NaN, `-1` the NaN with
-- every bit set, and `1` the signalling NaN with the lowest mantissa bit.
#guard farith "fsub" "f32" ["0x7f800000", "0x7f800000"] ["0"] == returns ["0x7fc00000"] 1
#guard farith "fsub" "f32" ["0x7f800000", "0x7f800000"] ["-1"] == returns ["0xffffffff"] 1
#guard farith "fsub" "f32" ["0x7f800000", "0x7f800000"] ["1"] == returns ["0x7f800001"] 1
-- The sign alone, with a zero mantissa, is the quiet NaN with its sign set.
#guard farith "fsub" "f32" ["0x7f800000", "0x7f800000"] ["-8388608"] == returns ["0xffc00000"] 1
-- A NaN result needs its choice, and a choice is a value of `i(m+1)`.
#guard farith "fdiv" "f64" ["0.0", "0.0"] [] ==
  misfit "the run makes choice 1, of type i53, and --choices gives 0 choices"
#guard farith "sqrt" "f16" ["-1.0"] ["1024"] == misfit "choice 1, 1024, is not a value of type i11"
-- `fneg` and `fabs` of a NaN, and an op on a NaN operand, are any NaN.
#guard farith "fneg" "f32" ["0x7fc00001"] ["-1"] == returns ["0xffffffff"] 1
#guard farith "fabs" "bf16" ["0xffff"] ["0"] == returns ["0x7fc0"] 1
#guard farith "fma" "f128" ["0x7fff8000000000000000000000000000", "1.0", "1.0"] ["0"] ==
  returns ["0x7fff8000000000000000000000000000"] 1
-- Exhaustive mode lists every NaN of `float<2,1>`, whose two NaNs are 7
-- and 15, written `0x7` and `0xf`.
#guard explore (floatOp "fsub" " round(rne)" "float(2, 1)" 2) ["0x6", "0x6"] ==
  outcomes [ret ["0x7"], ret ["0xf"]] 1

/-! # The rounding attribute -/

/-- What `fir-ref run` reports on `op` written with the attributes
`attr`. -/
def withAttr (op attr : String) (n : Nat) : RunReport :=
  runText (floatOp op attr "f32" n) "@f" ((List.replicate n "1.0"))

#guard withAttr "fadd" " round(rne)" 2 == returns ["2.0"]
#guard [("fadd", "", 2), ("fadd", " round(rtz)", 2), ("fmul", " rne", 2), ("sqrt", "", 1),
  ("fneg", " round(rne)", 1), ("fma", " round(rne) round(rne)", 3)].all fun (op, attr, n) =>
    (withAttr op attr n).status == 1

end FirTest
