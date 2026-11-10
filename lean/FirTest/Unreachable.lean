import FirTest.Branch

/-!
Tests of `unreachable` (#228) on `FirRef.runBytes`, which computes what
`fir-ref run` writes. A run that reaches it is immediate UB, with the
reason `unreachable reached`, at every width; a run that does not reach it
returns as it would without it; and a callee that reaches it is UB of its
caller. A function whose last call never returns ends that block with
`unreachable`, and its run runs out of fuel without reaching it. The text
decodes `unreachable` only with no attributes, operands or results, and
validation counts it as a terminator with no successors.
-/

namespace FirTest

open Fir FirRef

/-- `@f(%c: i1, %a: T) -> T`, which returns `%a` when `%c` is `true` and
reaches `unreachable` when it is `false`. -/
def guardAt (ty : String) : String :=
  body ("func @f(%c: i1, %a: " ++ ty ++ ") -> " ++ ty)
    ["^e:", "  cond_br %c, ^ok, ^dead @0", "^ok:", "  ret %a @0", "^dead:", "  unreachable @0"]

#guard selectWidths.all fun (ty, _, _) => valid (guardAt ty)
#guard selectWidths.all fun (ty, a, b) =>
  runText (guardAt ty) "@f" ["true", a] == returns [a] &&
    runText (guardAt ty) "@f" ["true", b] == returns [b] &&
    runText (guardAt ty) "@f" ["false", a] == ubBy "unreachable reached"
-- A poison value that the run returns does not reach `unreachable`.
#guard selectWidths.all fun (ty, _, _) =>
  runIn inferInstance (guardAt ty) ["true", "poison"] == some (returns ["poison"]) &&
    runIn inferInstance (guardAt ty) ["false", "poison"] == some (ubBy "unreachable reached")

/-- A function whose one block is `unreachable`, and a caller that calls
it when `%c` is `false`. -/
def callsNever : String :=
  oneFunc ("func @never() -> i8 {\n^e:\n  unreachable @0\n}\n\n" ++
    "func @f(%c: i1, %a: i8) -> i8 {\n^e:\n  cond_br %c, ^ok, ^bad @0\n^ok:\n  ret %a @0\n" ++
    "^bad:\n  %r: i8 = call @never @0\n  ret %r @0\n}\n")

#guard valid callsNever
#guard runText callsNever "@never" == ubBy "unreachable reached"
#guard runText callsNever "@f" ["true", "5"] == returns ["5"]
#guard runText callsNever "@f" ["false", "5"] == ubBy "unreachable reached"

/-- A function whose last call, to `@spin`, never returns. -/
def afterSpin : String :=
  oneFunc ("func @spin() {\n^e:\n  br ^l @0\n^l:\n  br ^l @0\n}\n\n" ++
    "func @f(%c: i1, %a: i64) -> i64 {\n^e:\n  cond_br %c, ^ok, ^fail @0\n^ok:\n  ret %a @0\n" ++
    "^fail:\n  call @spin @0\n  unreachable @0\n}\n")

#guard valid afterSpin
#guard runText afterSpin "@f" ["true", "-1"] == returns ["-1"]
#guard runText afterSpin "@f" ["false", "-1"] (fuel := 100) == exhausted

/-! # Text and validation -/

#guard !valid (body "func @f(%a: i8)" ["^e:", "  unreachable %a @0"])
#guard !valid (body "func @f()" ["^e:", "  unreachable now @0"])
#guard !valid (body "func @f()" ["^e:", "  %r: i8 = unreachable @0", "  ret @0"])
#guard checks (body "func @f()" ["^e:", "  unreachable ^b @0", "^b:", "  ret @0"])
  ["the op has 1 successors, and its op instance has 0"]
#guard checks (body "func @f()" ["^e:", "  unreachable @0", "  ret @0"])
  ["the op ends a block, and is not the last op of ^e"]

end FirTest
