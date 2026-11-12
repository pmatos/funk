import FirTest.Modes

/-!
Tests of #229's float constants and `fcmp` on `FirRef.runBytes`, which
computes what `fir-ref run` writes. A float argument, result or constant is
the one float literal of its bits (ADR-2026-11-11-1438), and `poison` is an
argument of every float type. `fcmp` runs with each of its fourteen
predicates (ADR-2026-11-09-1549) at `f32`, `f64`, `f16`, `bf16`, `f128` and
`float<2,1>`, on zeros of both signs, subnormals, ones, the largest finite
values, infinities and NaNs, quiet and signalling, with payloads and either
sign.
-/

namespace FirTest

open Fir FirRef

/-- `@f(%a: T, %b: T) -> i1`, which returns `fcmp P %a, %b`. -/
def fcmpAt (p ty : String) : String :=
  body ("func @f(%a: " ++ ty ++ ", %b: " ++ ty ++ ") -> i1")
    ["^e:", "  %s: i1 = fcmp " ++ p ++ " %a, %b @0", "  ret %s @0"]

/-- What `fir-ref run` reports on `fcmp P %a, %b` at the type `ty`, for each
predicate `P` in the order of `FPred.all`. -/
def fcmpAll (ty a b : String) : List RunReport :=
  Core.FPred.all.map fun p => runText (fcmpAt p.name ty) "@f" [a, b]

/-- The reports of runs that return what the fourteen predicates give on a
pair that compares as `c`, where `none` is unordered. -/
def fordered (c : Option Ordering) : List RunReport :=
  (Core.fpredResults c).map fun r => returns [toString r]

/-! # Arguments, results and constants -/

/-- `@f(%a: T) -> T`, which returns its argument. -/
def floatId (ty : String) : String :=
  body ("func @f(%a: " ++ ty ++ ") -> " ++ ty) ["^e:", "  ret %a @0"]

-- A float passes through as its bits: `1.0`, `-0`, the largest negative
-- finite value, NaNs with their sign set or a payload, at `f32`.
#guard ["1.0", "-0.0", "-3.4028235e38", "0xffffffff", "0.0", "0x7fc00001"].all fun a =>
  runText (floatId "f32") "@f" [a] == returns [a]
#guard ["0x7ff0000000000001", "-0.0", "1.0"].all fun a =>
  runText (floatId "f64") "@f" [a] == returns [a]
#guard runText (floatId "float(2, 1)") "@f" ["0xf"] == returns ["0xf"]
#guard runText (floatId "f128") "@f" ["0x7fff0000000000000000000000000000"] ==
  returns ["0x7fff0000000000000000000000000000"]
-- `poison` is an argument of a float type, and is returned as it is.
#guard runText (floatId "bf16") "@f" ["poison"] == returns ["poison"]

/-- The report of an argument that is not a value of its type. -/
def notValue (a ty : String) : RunReport :=
  { err := "fir-ref: " ++ a ++ " is not a value of type " ++ ty, status := 2 }

-- A bit pattern has one spelling: the bits read as an integer, a decimal
-- with a trailing zero, a finite value in hexadecimal, hexadecimal bits of
-- the wrong width, `true` and `+1.0` are not values of their type.
#guard runText (floatId "f32") "@f" ["1065353216"] == notValue "1065353216" "f32"
#guard runText (floatId "f32") "@f" ["1.50"] == notValue "1.50" "f32"
#guard runText (floatId "f32") "@f" ["0x3f800000"] == notValue "0x3f800000" "f32"
#guard runText (floatId "f16") "@f" ["0x07e00"] == notValue "0x07e00" "f16"
#guard runText (floatId "f32") "@f" ["true"] == notValue "true" "f32"
#guard runText (floatId "f32") "@f" ["+1.0"] == notValue "+1.0" "f32"
#guard runText (floatId "f32") "@f" [" 1.0"] == notValue " 1.0" "f32"

/-- `@f() -> T`, which returns the constant `v` of type `T`. -/
def floatConst (ty v : String) : String :=
  body ("func @f() -> " ++ ty) ["^e:", "  %c: " ++ ty ++ " = const " ++ v ++ " @0", "  ret %c @0"]

-- A constant gives its bits, each NaN's payload and sign included. A
-- decimal reads as its value rounded to the format, so `0.1` at `f32` is
-- the float nearest it, and gives back `0.1`, its shortest spelling. The
-- largest finite `f16`, 65504, is spelled `65500.0`, which reads back to it,
-- and `65504.0` is not a spelling.
#guard runText (floatConst "f32" "0.1") "@f" == returns ["0.1"]
#guard runText (floatConst "f128" "0.1") "@f" == returns ["0.1"]
#guard runText (floatConst "f16" "65500.0") "@f" == returns ["65500.0"]
#guard runText (floatId "f16") "@f" ["65504.0"] == notValue "65504.0" "f16"
#guard ["0x7fc00000", "0xffc00000", "0x7f800001", "0xffffffff", "1.0e-45", "-0.0"].all fun v =>
  runText (floatConst "f32" v) "@f" == returns [v]
#guard runText (floatConst "f64" "-1.7976931348623157e308") "@f" ==
  returns ["-1.7976931348623157e308"]
#guard runText (floatConst "f16" "0x7c01") "@f" == returns ["0x7c01"]

/-! # `fcmp` at every format -/

-- At `f32`: `1.0 < 2.0`, `-0 = +0`, the smallest subnormals of either sign,
-- `-inf` below the most negative finite value, and NaNs.
#guard fcmpAll "f32" "1.0" "2.0" == fordered (some .lt)
#guard fcmpAll "f32" "-0.0" "0.0" == fordered (some .eq)
#guard fcmpAll "f32" "1.0e-45" "-1.0e-45" == fordered (some .gt)
#guard fcmpAll "f32" "0xff800000" "-3.4028235e38" == fordered (some .lt)
#guard fcmpAll "f32" "0x7f800000" "0x7f800000" == fordered (some .eq)
#guard fcmpAll "f32" "0x7fc00000" "1.0" == fordered none
#guard fcmpAll "f32" "0xffc00000" "0xffc00000" == fordered none
#guard fcmpAll "f32" "0.0" "0x7f800001" == fordered none
-- At `f64`: the largest finite value against `+inf`, `-1.0` against `+0`,
-- and a signalling NaN with its sign set against itself.
#guard fcmpAll "f64" "1.7976931348623157e308" "0x7ff0000000000000" == fordered (some .lt)
#guard fcmpAll "f64" "-1.0" "0.0" == fordered (some .lt)
#guard fcmpAll "f64" "0xfff0000000000001" "0xfff0000000000001" == fordered none
-- At `f16`, `bf16`, `f128` and `float<2,1>`.
#guard fcmpAll "f16" "0xfc00" "-65500.0" == fordered (some .lt)
#guard fcmpAll "bf16" "1.0" "1.0" == fordered (some .eq)
#guard fcmpAll "f128" "0x7fff8000000000000000000000000000" "0.0" == fordered none
#guard fcmpAll "f128" "0x7fff0000000000000000000000000000" "0.0" == fordered (some .gt)
#guard fcmpAll "float(2, 1)" "0.5" "3.0" == fordered (some .lt)
#guard fcmpAll "float(2, 1)" "-0.0" "0.0" == fordered (some .eq)
#guard fcmpAll "float(2, 1)" "0x7" "0x6" == fordered none

-- A poison operand gives poison, with every predicate, in either place.
#guard Core.FPred.all.all fun p =>
  runText (fcmpAt p.name "f32") "@f" ["poison", "0.0"] == returns ["poison"] &&
    runText (fcmpAt p.name "f64") "@f" ["0x7ff8000000000000", "poison"] == returns ["poison"] &&
    runText (fcmpAt p.name "f16") "@f" ["poison", "poison"] == returns ["poison"]

-- A constant compared with an argument: `fcmp oeq` of a NaN constant with
-- itself is `false`, and `fcmp une` `true`.
#guard runText (body "func @f() -> i1, i1"
    ["^e:", "  %n: f32 = const 0x7fc00000 @0", "  %e: i1 = fcmp oeq %n, %n @0",
     "  %u: i1 = fcmp une %n, %n @0", "  ret %e, %u @0"]) "@f" == returns ["false", "true"]

end FirTest
