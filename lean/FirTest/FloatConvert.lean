import FirTest.Modes

/-!
Tests of #241's conversions between float formats, `fpext` and `fptrunc`,
on `FirRef.runBytes`, which computes what `fir-ref run` writes
(ADR-2026-11-09-1549). The corpus, `float-fpext-f32-f64`,
`float-fptrunc-f64-f32`, `float-fpext-odd` and `float-fptrunc-odd`,
converts the boundary values of each pair of aliased formats against
`scripts/harness/float_ref.py`; these check what it does not: that a
conversion of a number takes no choice, in scripted and in exhaustive
mode, that a NaN is the NaN its choice names, that a conversion composes
with another, and that `fpext` without attributes and `fptrunc` with
`round(rne)` are the only spellings that decode.
-/

namespace FirTest

open Fir FirRef

/-- `@f` from `src` to `dst`, which returns `op %a` with the attributes
`attr`. -/
def convText (op src dst : String) (attr : String := "") : String :=
  body ("func @f(%a: " ++ src ++ ") -> " ++ dst)
    ["^e:", "  %r: " ++ dst ++ " = " ++ op ++ attr ++ " %a @0", "  ret %r @0"]

/-- What scripted mode reports on `fpext` from `src` to `dst` of `arg`,
with `cs`. -/
def ext (src dst arg : String) (cs : List String := []) : RunReport :=
  runText (convText "fpext" src dst) "@f" [arg] (mode := .scripted cs)

/-- What scripted mode reports on `fptrunc` from `src` to `dst` of `arg`,
with `cs`. -/
def trunc (src dst arg : String) (cs : List String := []) : RunReport :=
  runText (convText "fptrunc" src dst " round(rne)") "@f" [arg] (mode := .scripted cs)

-- `fpext` keeps the number: `f32`'s `0.1` is not `f64`'s nearest `0.1`.
#guard ext "f32" "f64" "0.1" == returns ["0.10000000149011612"]
#guard ext "f16" "f128" "65500.0" == returns ["65504.0"]
#guard ext "bf16" "f32" "-1.0" == returns ["-1.0"]
-- `f32`'s smallest subnormal, `2^-149`, is a normal `f64`.
#guard ext "f32" "f64" "1.0e-45" == returns ["1.401298464324817e-45"]
-- Zeros and infinities keep their sign.
#guard ext "f32" "f64" "-0.0" == returns ["-0.0"]
#guard ext "f16" "f128" "0xfc00" == returns ["0xffff0000000000000000000000000000"]
-- `fptrunc` rounds to nearest even: `1 + 2^-24` is halfway between `f32`'s
-- `1` and `1 + 2^-23` and goes to `1`; `1 + 3 * 2^-24` goes up.
#guard trunc "f64" "f32" "1.0000000596046448" == returns ["1.0"]
#guard trunc "f64" "f32" "1.0000001788139343" == returns ["1.0000002"]
-- A number too large for the target is an infinity of its sign, and one
-- too small is a zero of its sign.
#guard trunc "f64" "f32" "1.0e300" == returns ["0x7f800000"]
#guard trunc "f64" "f32" "-1.0e300" == returns ["0xff800000"]
#guard trunc "f64" "f32" "7.006492321624085e-46" == returns ["0.0"]
#guard trunc "f64" "f32" "-7.006492321624085e-46" == returns ["-0.0"]
-- At `f16`, `65519` rounds to the largest finite value, `65504`, and
-- `65520`, halfway to `2^16`, to `+∞`.
#guard trunc "f32" "f16" "65519.0" == returns ["65500.0"]
#guard trunc "f32" "f16" "65520.0" == returns ["0x7c00"]
-- Between `bf16` and `f16`, neither holds the other: `bf16`'s `2^-25`,
-- half of `f16`'s smallest subnormal, goes to `+0`, and `f16`'s
-- `1 + 2^-8`, halfway between two `bf16` values, to `1`.
#guard trunc "bf16" "f16" "2.98e-8" == returns ["0.0"]
#guard trunc "f16" "bf16" "1.004" == returns ["1.0"]
#guard trunc "bf16" "f16" "3.39e38" == returns ["0x7c00"]
-- A NaN is any NaN of the target: the choice of `m' + 1` bits names it.
#guard ext "f32" "f64" "0x7fc00001" ["0"] == returns ["0x7ff8000000000000"] 1
#guard ext "f32" "f64" "0x7f800001" ["-1"] == returns ["0xffffffffffffffff"] 1
#guard trunc "f64" "f32" "0xfff8000000000000" ["1"] == returns ["0x7f800001"] 1
#guard trunc "f64" "f32" "0x7ff8000000000000" [] ==
  misfit "the run makes choice 1, of type i24, and --choices gives 0 choices"
-- A poison operand gives poison.
#guard ext "f32" "f64" "poison" == returns ["poison"]
#guard trunc "f128" "bf16" "poison" == returns ["poison"]
-- Exhaustive mode finds one outcome on a number, and every NaN of the
-- target on a NaN.
-- At `float<2,1>`, `2.5` is halfway between `2` and `3` and goes to `2`,
-- and `3.5`, halfway past the largest finite value, to `+∞`.
#guard explore (convText "fptrunc" "f16" "float(2, 1)" " round(rne)") ["2.5"] ==
  outcomes [ret ["2.0"]] 0
#guard explore (convText "fptrunc" "f16" "float(2, 1)" " round(rne)") ["3.5"] ==
  outcomes [ret ["0x6"]] 0
#guard explore (convText "fptrunc" "f16" "float(2, 1)" " round(rne)") ["0x7e00"] ==
  outcomes [ret ["0x7"], ret ["0xf"]] 1

/-- `@f(%a: f32) -> f32`: `a` taken to `f64` and back, which gives `a`. -/
def roundTrip : String :=
  body "func @f(%a: f32) -> f32"
    ["^e:", "  %d: f64 = fpext %a @0", "  %r: f32 = fptrunc round(rne) %d @0", "  ret %r @0"]

#guard runText roundTrip "@f" ["0.1"] == returns ["0.1"]
#guard runText roundTrip "@f" ["1.0e-45"] == returns ["1.0e-45"]

-- `fpext` has no attribute and `fptrunc` needs `round(rne)`, and each takes
-- a float to a float: any other spelling does not decode.
#guard [("fpext", "f32", "f64", " round(rne)"), ("fptrunc", "f64", "f32", ""),
  ("fptrunc", "f64", "f32", " round(rtz)"), ("fpext", "i32", "f64", ""),
  ("fptrunc", "f64", "i32", " round(rne)")].all
    fun (op, src, dst, attr) => (runText (convText op src dst attr) "@f" ["0"]).status == 1

end FirTest
