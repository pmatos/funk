import FirTest.Modes

/-!
Tests of #241's conversions from integers to floats, `sitofp` and
`uitofp`, on `FirRef.runBytes`, which computes what `fir-ref run` writes
(ADR-2026-11-09-1549). The corpus, `float-sitofp-T`, `float-uitofp-T` and
`float-itofp-odd`, converts the boundary integers of each width to each
format against `scripts/harness/float_ref.py`; these check what it does
not: that a conversion takes no choice, in scripted and in exhaustive
mode, that it composes with the float arithmetic, and that a conversion
without `round(rne)`, or whose types are not an integer and a float, does
not decode.
-/

namespace FirTest

open Fir FirRef

/-- `@f` from `src` to `dst`, which returns `op %a` with the attributes
`attr`. -/
def itofpText (op src dst : String) (attr : String := " round(rne)") : String :=
  body ("func @f(%a: " ++ src ++ ") -> " ++ dst)
    ["^e:", "  %r: " ++ dst ++ " = " ++ op ++ attr ++ " %a @0", "  ret %r @0"]

/-- What scripted mode reports on `op` from `src` to `dst` of `arg`. -/
def itofp (op src dst arg : String) : RunReport :=
  runText (itofpText op src dst) "@f" [arg] (mode := .scripted [])

-- The bits read as signed, and as unsigned.
#guard itofp "sitofp" "i8" "f32" "-1" == returns ["-1.0"]
#guard itofp "uitofp" "i8" "f32" "-1" == returns ["255.0"]
#guard itofp "sitofp" "i1" "f64" "true" == returns ["-1.0"]
#guard itofp "uitofp" "i1" "f64" "true" == returns ["1.0"]
-- Zero is `+0` for both.
#guard itofp "sitofp" "i32" "f32" "0" == returns ["0.0"]
#guard itofp "uitofp" "i64" "f16" "0" == returns ["0.0"]
-- `2^24 + 1` is halfway between two `f32` values and goes to the even one;
-- `2^24 + 3` goes up.
#guard itofp "sitofp" "i32" "f32" "16777217" == returns ["16777216.0"]
#guard itofp "sitofp" "i32" "f32" "16777219" == returns ["16777220.0"]
#guard itofp "sitofp" "i32" "f32" "-16777217" == returns ["-16777216.0"]
-- Too large for the format is an infinity of its sign: at `f16`, `65519`
-- is the largest finite value and `65520` is `+∞`.
#guard itofp "uitofp" "i32" "f16" "65519" == returns ["65500.0"]
#guard itofp "uitofp" "i32" "f16" "65520" == returns ["0x7c00"]
#guard itofp "sitofp" "i32" "f16" "-65520" == returns ["0xfc00"]
-- The widest integers: `2^127` and `-2^127` are exact at `f32`, and
-- `2^128 - 1` rounds to `2^128`, past the largest `f32`, so it is `+∞`.
#guard itofp "sitofp" "i128" "f32" "-170141183460469231731687303715884105728" ==
  returns ["-1.7014118e38"]
#guard itofp "uitofp" "i128" "f32" "-1" == returns ["0x7f800000"]
#guard itofp "uitofp" "i128" "f128" "-1" == returns ["3.402823669209384634633746074317682e38"]
-- At `bf16`, with 8 bits of precision, `257` is a tie and goes to `256`.
#guard itofp "uitofp" "i16" "bf16" "257" == returns ["256.0"]
#guard itofp "uitofp" "i16" "bf16" "259" == returns ["260.0"]
-- At `float<2,1>`, whose largest finite value is `3`, `4` overflows.
#guard itofp "sitofp" "i8" "float(2, 1)" "3" == returns ["3.0"]
#guard itofp "sitofp" "i8" "float(2, 1)" "4" == returns ["0x6"]
-- A poison operand gives poison.
#guard itofp "sitofp" "i32" "f32" "poison" == returns ["poison"]
#guard itofp "uitofp" "i64" "f64" "poison" == returns ["poison"]
-- Exhaustive mode finds one outcome on every `i4`: a conversion chooses
-- nothing.
#guard explore (itofpText "sitofp" "i4" "float(2, 1)") ["-1"] == outcomes [ret ["-1.0"]] 0
#guard explore (itofpText "uitofp" "i4" "f16") ["-1"] == outcomes [ret ["15.0"]] 0

/-- `@f(%a: i32) -> f32`: `a` converted, plus `0.5`, so a conversion feeds
the float arithmetic. -/
def halfMore : String :=
  body "func @f(%a: i32) -> f32"
    ["^e:", "  %x: f32 = sitofp round(rne) %a @0", "  %h: f32 = const 0.5 @0",
     "  %r: f32 = fadd round(rne) %x, %h @0", "  ret %r @0"]

#guard runText halfMore "@f" ["-3"] == returns ["-2.5"]

-- Without `round(rne)`, with another mode, from a float, to an integer, or
-- with two operands, a conversion does not decode.
#guard [("sitofp", "i32", "f32", ""), ("uitofp", "i32", "f32", " round(rtz)"),
  ("sitofp", "f32", "f32", " round(rne)"), ("uitofp", "i32", "i64", " round(rne)")].all
    fun (op, src, dst, attr) => (runText (itofpText op src dst attr) "@f" ["0"]).status == 1

end FirTest
