import FirTest.Modes

/-!
Tests of #241's bit casts on `FirRef.runBytes`, which computes what
`fir-ref run` writes (ADR-2026-11-09-1549). The corpus, `float-bitcast-T`,
casts the edges of each format both ways; these check what it does not:
that a bit cast takes no choice, even to a NaN, in scripted and in
exhaustive mode, that it composes with the float arithmetic, and that a
cast whose widths differ, or with an attribute, does not decode.
-/

namespace FirTest

open Fir FirRef

/-- `@f` from `src` to `dst`, which returns `bitcast %a` with the
attributes `attr`. -/
def bitcastText (src dst : String) (attr : String := "") : String :=
  body ("func @f(%a: " ++ src ++ ") -> " ++ dst)
    ["^e:", "  %r: " ++ dst ++ " = bitcast" ++ attr ++ " %a @0", "  ret %r @0"]

/-- What scripted mode reports on a bit cast from `src` to `dst` of `arg`. -/
def bitcast (src dst arg : String) : RunReport :=
  runText (bitcastText src dst) "@f" [arg] (mode := .scripted [])

-- The bits come through both ways, with no choice, at every format.
#guard bitcast "f32" "i32" "1.0" == returns ["1065353216"]
#guard bitcast "i32" "f32" "1065353216" == returns ["1.0"]
#guard bitcast "f64" "i64" "-0.0" == returns ["-9223372036854775808"]
#guard bitcast "i16" "f16" "31744" == returns ["0x7c00"]
#guard bitcast "bf16" "i16" "-1.0" == returns ["-16512"]
#guard bitcast "i128" "f128" "1" == returns ["6.0e-4966"]
#guard bitcast "float(2, 1)" "i4" "0x7" == returns ["7"]
-- A NaN's sign and payload come through, a signalling NaN's too: no NaN
-- is chosen, so no choice is needed.
#guard bitcast "f32" "i32" "0xffc00001" == returns ["-4194303"]
#guard bitcast "i32" "f32" "2139095041" == returns ["0x7f800001"]
#guard bitcast "i64" "f64" "-1" == returns ["0xffffffffffffffff"]
-- A poison operand gives poison.
#guard bitcast "f32" "i32" "poison" == returns ["poison"]
#guard bitcast "i64" "f64" "poison" == returns ["poison"]
-- Exhaustive mode finds one outcome: the cast chooses nothing.
#guard explore (bitcastText "i4" "float(2, 1)") ["-1"] == outcomes [ret ["0xf"]] 0

/-- `@f(%a: f32) -> i32`: the bits of `-(a + a)`, which flips the sign with
`xor` after the cast. -/
def negBits : String :=
  body "func @f(%a: f32) -> i32"
    ["^e:", "  %s: f32 = fadd round(rne) %a, %a @0", "  %b: i32 = bitcast %s @0",
     "  %m: i32 = const -2147483648 @0", "  %r: i32 = xor %b, %m @0", "  ret %r @0"]

#guard runText negBits "@f" ["1.5"] == returns ["-1069547520"]

-- Widths that differ, two floats, two integers or an attribute do not
-- decode.
#guard [("f32", "i64", ""), ("i32", "f64", ""), ("f16", "bf16", ""), ("i32", "i32", ""),
  ("f32", "i32", " round(rne)")].all fun (src, dst, attr) =>
    (runText (bitcastText src dst attr) "@f" ["0"]).status == 1

end FirTest
