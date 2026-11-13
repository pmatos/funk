import FirTest.Modes

/-!
Tests of #241's conversions from floats to integers, `fptosi` and
`fptoui`, on `FirRef.runBytes`, which computes what `fir-ref run` writes
(ADR-2026-11-09-1549; the human's ruling of 2026-11-12 on #354). The
corpus, `float-fptosi-T`, `float-fptoui-T`, `float-fptosi-odd` and
`float-fptoui-odd`, converts the boundary values of each format to each width against
`scripts/harness/float_ref.py`; these check what it does not: that a
conversion takes no choice, in scripted and in exhaustive mode, that it
composes with the float arithmetic, and that a conversion with an
attribute, or whose types are not a float and an integer, does not decode.
-/

namespace FirTest

open Fir FirRef

/-- `@f` from `src` to `dst`, which returns `op %a` with the attributes
`attr`. -/
def fptoiText (op src dst : String) (attr : String := "") : String :=
  body ("func @f(%a: " ++ src ++ ") -> " ++ dst)
    ["^e:", "  %r: " ++ dst ++ " = " ++ op ++ attr ++ " %a @0", "  ret %r @0"]

/-- What scripted mode reports on `op` from `src` to `dst` of `arg`. -/
def fptoi (op src dst arg : String) : RunReport :=
  runText (fptoiText op src dst) "@f" [arg] (mode := .scripted [])

-- The fraction is cut off toward zero: `2.7` gives `2`, `-2.7` gives `-2`.
#guard fptoi "fptosi" "f32" "i32" "2.7" == returns ["2"]
#guard fptoi "fptosi" "f32" "i32" "-2.7" == returns ["-2"]
#guard fptoi "fptoui" "f64" "i8" "255.9" == returns ["-1"]
-- `-0.5` and `-0.0` truncate to `0`, which `fptoui` holds; `-1.0` it does not.
#guard fptoi "fptoui" "f32" "i32" "-0.5" == returns ["0"]
#guard fptoi "fptoui" "f16" "i32" "-0.0" == returns ["0"]
#guard fptoi "fptoui" "f32" "i32" "-1.0" == returns ["poison"]
-- At `i32`, the largest `f32` below `2^31` is in range and `2^31` is not;
-- `-2^31` is, and the `f32` below it is not.
#guard fptoi "fptosi" "f32" "i32" "2147483500.0" == returns ["2147483520"]
#guard fptoi "fptosi" "f32" "i32" "2147483600.0" == returns ["poison"]
#guard fptoi "fptosi" "f32" "i32" "-2147483600.0" == returns ["-2147483648"]
#guard fptoi "fptosi" "f32" "i32" "-2147484000.0" == returns ["poison"]
-- `fptoui` holds `2^31` at `i32`, and not `2^32`.
#guard fptoi "fptoui" "f32" "i32" "2147483600.0" == returns ["-2147483648"]
#guard fptoi "fptoui" "f32" "i32" "4294967300.0" == returns ["poison"]
-- `i1` holds `-1` and `0` signed, and `0` and `1` unsigned.
#guard fptoi "fptosi" "f64" "i1" "-1.5" == returns ["true"]
#guard fptoi "fptosi" "f64" "i1" "1.0" == returns ["poison"]
#guard fptoi "fptoui" "f64" "i1" "1.9" == returns ["true"]
#guard fptoi "fptoui" "f64" "i1" "2.0" == returns ["poison"]
-- Infinities and NaNs are poison; the smallest subnormal is `0`.
#guard fptoi "fptosi" "f64" "i64" "0x7ff0000000000000" == returns ["poison"]
#guard fptoi "fptoui" "f32" "i64" "0x7fc00001" == returns ["poison"]
#guard fptoi "fptosi" "f32" "i64" "1.0e-45" == returns ["0"]
-- The widest: `-2^127` is in range at `i128`, and `f32`'s largest finite
-- value, below `2^128`, is in range unsigned and not signed.
#guard fptoi "fptosi" "f64" "i128" "-1.7014118346046923e38" ==
  returns ["-170141183460469231731687303715884105728"]
#guard fptoi "fptoui" "f32" "i128" "3.4028235e38" ==
  returns ["-20282409603651670423947251286016"]
#guard fptoi "fptosi" "f32" "i128" "3.4028235e38" == returns ["poison"]
-- `f128`'s largest finite value is poison at `i128`, and `bf16`'s `256.0`
-- is too large for `i8`.
#guard fptoi "fptosi" "f128" "i128" "1.189731495357231765085759326628007e4932" ==
  returns ["poison"]
#guard fptoi "fptoui" "bf16" "i8" "256.0" == returns ["poison"]
#guard fptoi "fptoui" "bf16" "i8" "255.0" == returns ["-1"]
-- At `float<2,1>`, whose largest finite value is `3`, `3.0` fits `i2`
-- unsigned and not signed.
#guard fptoi "fptoui" "float(2, 1)" "i2" "3.0" == returns ["-1"]
#guard fptoi "fptosi" "float(2, 1)" "i2" "3.0" == returns ["poison"]
-- A poison operand gives poison.
#guard fptoi "fptosi" "f32" "i32" "poison" == returns ["poison"]
#guard fptoi "fptoui" "f64" "i64" "poison" == returns ["poison"]
-- Exhaustive mode finds one outcome: a conversion chooses nothing, not even
-- on a NaN.
#guard explore (fptoiText "fptosi" "float(2, 1)" "i4") ["-3.0"] == outcomes [ret ["-3"]] 0
#guard explore (fptoiText "fptoui" "f16" "i8") ["0x7e00"] == outcomes [ret ["poison"]] 0

/-- `@f(%a: f32) -> i32`: `a` plus `0.5`, truncated, so a conversion takes
the float arithmetic's result. -/
def halfUp : String :=
  body "func @f(%a: f32) -> i32"
    ["^e:", "  %h: f32 = const 0.5 @0", "  %x: f32 = fadd round(rne) %a, %h @0",
     "  %r: i32 = fptosi %x @0", "  ret %r @0"]

#guard runText halfUp "@f" ["2.6"] == returns ["3"]
#guard runText halfUp "@f" ["-2.6"] == returns ["-2"]

-- With `round(rne)` or `round(rtz)`, from an integer, to a float, or with
-- two operands, a conversion does not decode.
#guard [("fptosi", "f32", "i32", " round(rne)"), ("fptoui", "f32", "i32", " round(rtz)"),
  ("fptosi", "i32", "i32", ""), ("fptoui", "f32", "f64", "")].all
    fun (op, src, dst, attr) => (runText (fptoiText op src dst attr) "@f" ["0"]).status == 1

end FirTest
