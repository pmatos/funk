import FirTest.Modes

/-!
Tests of #229's float constants and `fcmp` on `FirRef.runBytes`, which
computes what `fir-ref run` writes. A float argument, result or constant is
its bits read as a signed integer (ADR-2026-11-11-1138), and `poison` is an
argument of every float type. `fcmp` runs with each of its fourteen
predicates (ADR-2026-11-11-1139) at `f32`, `f64`, `f16`, `bf16`, `f128` and
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
-- finite value and a NaN with its sign set and a payload, at `f32`.
#guard ["1065353216", "-2147483648", "-8388609", "-1", "0", "2143289345"].all fun a =>
  runText (floatId "f32") "@f" [a] == returns [a]
#guard ["9218868437227405313", "-9223372036854775808", "4607182418800017408"].all fun a =>
  runText (floatId "f64") "@f" [a] == returns [a]
#guard runText (floatId "float(2, 1)") "@f" ["-1"] == returns ["-1"]
#guard runText (floatId "f128") "@f" ["170135991163610696904058773219554885632"] ==
  returns ["170135991163610696904058773219554885632"]
-- `poison` is an argument of a float type, and is returned as it is.
#guard runText (floatId "bf16") "@f" ["poison"] == returns ["poison"]

/-- The report of an argument that is not a value of its type. -/
def notValue (a ty : String) : RunReport :=
  { err := "fir-ref: " ++ a ++ " is not a value of type " ++ ty, status := 2 }

-- A bit pattern has one spelling: the unsigned reading of `-0` is out of
-- range, and so are `true` and a decimal float.
#guard runText (floatId "f32") "@f" ["2147483648"] == notValue "2147483648" "f32"
#guard runText (floatId "f16") "@f" ["32768"] == notValue "32768" "f16"
#guard runText (floatId "f32") "@f" ["true"] == notValue "true" "f32"
#guard runText (floatId "f32") "@f" ["1.5"] == notValue "1.5" "f32"
#guard runText (floatId "f32") "@f" ["+1"] == notValue "+1" "f32"

/-- `@f() -> T`, which returns the constant `v` of type `T`. -/
def floatConst (ty v : String) : String :=
  body ("func @f() -> " ++ ty) ["^e:", "  %c: " ++ ty ++ " = const " ++ v ++ " @0", "  ret %c @0"]

-- A constant gives its bits, each NaN's payload and sign included.
#guard ["2143289344", "-4194304", "2139095041", "-1", "1", "-2147483648"].all fun v =>
  runText (floatConst "f32" v) "@f" == returns [v]
#guard runText (floatConst "f64" "-4503599627370497") "@f" == returns ["-4503599627370497"]
#guard runText (floatConst "f16" "31745") "@f" == returns ["31745"]

/-! # `fcmp` at every format -/

-- At `f32`: `1.0 < 2.0`, `-0 = +0`, the smallest subnormals of either sign,
-- `-inf` below the most negative finite value, and NaNs.
#guard fcmpAll "f32" "1065353216" "1073741824" == fordered (some .lt)
#guard fcmpAll "f32" "-2147483648" "0" == fordered (some .eq)
#guard fcmpAll "f32" "1" "-2147483647" == fordered (some .gt)
#guard fcmpAll "f32" "-8388608" "-8388609" == fordered (some .lt)
#guard fcmpAll "f32" "2139095040" "2139095040" == fordered (some .eq)
#guard fcmpAll "f32" "2143289344" "1065353216" == fordered none
#guard fcmpAll "f32" "-4194304" "-4194304" == fordered none
#guard fcmpAll "f32" "0" "2139095041" == fordered none
-- At `f64`: the largest finite value against `+inf`, `-1.0` against `+0`,
-- and a signalling NaN with its sign set against itself.
#guard fcmpAll "f64" "9218868437227405311" "9218868437227405312" == fordered (some .lt)
#guard fcmpAll "f64" "-4616189618054758400" "0" == fordered (some .lt)
#guard fcmpAll "f64" "-4503599627370495" "-4503599627370495" == fordered none
-- At `f16`, `bf16`, `f128` and `float<2,1>`.
#guard fcmpAll "f16" "-1024" "-1025" == fordered (some .lt)
#guard fcmpAll "bf16" "16256" "16256" == fordered (some .eq)
#guard fcmpAll "f128" "170138587312039964317873038467719495680" "0" == fordered none
#guard fcmpAll "f128" "170135991163610696904058773219554885632" "0" == fordered (some .gt)
#guard fcmpAll "float(2, 1)" "1" "5" == fordered (some .lt)
#guard fcmpAll "float(2, 1)" "-8" "0" == fordered (some .eq)
#guard fcmpAll "float(2, 1)" "7" "6" == fordered none

-- A poison operand gives poison, with every predicate, in either place.
#guard Core.FPred.all.all fun p =>
  runText (fcmpAt p.name "f32") "@f" ["poison", "0"] == returns ["poison"] &&
    runText (fcmpAt p.name "f64") "@f" ["2143289344", "poison"] == returns ["poison"] &&
    runText (fcmpAt p.name "f16") "@f" ["poison", "poison"] == returns ["poison"]

-- A constant compared with an argument: `fcmp oeq` of a NaN constant with
-- itself is `false`, and `fcmp une` `true`.
#guard runText (body "func @f() -> i1, i1"
    ["^e:", "  %n: f32 = const 2143289344 @0", "  %e: i1 = fcmp oeq %n, %n @0",
     "  %u: i1 = fcmp une %n, %n @0", "  ret %e, %u @0"]) "@f" == returns ["false", "true"]

end FirTest
