import FirTest.Branch

/-!
Tests of loops on `FirRef.runBytes`, which computes what `fir-ref run`
writes: the spec's example `@sum`, and the same loop at `i1`, `i7`, `i8`,
`i33` and `i64`; an iterative factorial and Euclid's gcd at those widths
and `i128`; block arguments that swap or rotate each other on every trip
round a loop; and loops that never end, which run out of fuel at the
budget that a run sets. Every function that these tests run is valid.
-/

namespace FirTest

open Fir FirRef

/-- The constant `n` as text writes it at the type `ty`: `false` and
`true` for `0` and `1` at `i1`. -/
def lit (ty : String) (n : Nat) : String :=
  if ty == "i1" then (if n == 0 then "false" else "true") else toString n

/-! # The spec's example

`@sum` adds the integers from `0` up to, but not including, `%n`. Its
`@sum10` calls it, so it waits for `call`'s rules (#20). -/

/-- The spec's example module, as text. -/
def sumText : String := Example.sumModule.print

#guard valid sumText
#guard runText sumText "@sum" ["10"] == returns ["45"]
#guard runText sumText "@sum" ["0"] == returns ["0"]
#guard runText sumText "@sum" ["1"] == returns ["0"]
#guard runText sumText "@sum" ["2"] == returns ["1"]
#guard runText sumText "@sum" ["-3"] == returns ["0"]
#guard runText sumText "@sum" ["100"] (mode := .exhaustive 16) ==
  outcomes [ret ["4950"]] 0
#guard runText sumText "@sum10" == fails 2 "fir-ref: @sum10: call @sum has no execution rules yet"
-- `@sum` on `%n ≥ 0` takes `6 * %n + 5` steps: two in `^entry`, two in each
-- of the `%n + 1` visits of `^loop`, four in each of the `%n` runs of
-- `^body`, and one in `^exit`.
#guard runText sumText "@sum" ["10"] (fuel := 65) == returns ["45"]
#guard runText sumText "@sum" ["10"] (fuel := 64) == exhausted

/-- `@f(%n: T) -> T`: the loop of `@sum` at the type `ty`. -/
def sumAt (ty : String) : String :=
  body ("func @f(%n: " ++ ty ++ ") -> " ++ ty)
    ["^entry:", "  %zero: " ++ ty ++ " = const " ++ lit ty 0 ++ " @0",
     "  br ^loop(%zero, %zero) @0", "^loop(%i: " ++ ty ++ ", %acc: " ++ ty ++ "):",
     "  %done: i1 = icmp sge %i, %n @0", "  cond_br %done, ^exit(%acc), ^body @0", "^body:",
     "  %acc1: " ++ ty ++ " = add nsw %acc, %i @0",
     "  %one: " ++ ty ++ " = const " ++ lit ty 1 ++ " @0",
     "  %i1: " ++ ty ++ " = add nsw %i, %one @0",
     "  br ^loop(%i1, %acc1) @0", "^exit(%r: " ++ ty ++ "):", "  ret %r @0"]

/-- What `fir-ref run` reports on `@f` of `t` at each argument vector of
`cases`, and the values it should return there. The budget of `10000`
steps is ample for every loop below, so a rule that broke one of them
fails its guard here rather than running to the default budget. -/
def loopRuns (t : String) (cases : List (List String × String)) : Bool :=
  valid t && cases.all fun (args, v) => runText t "@f" args (fuel := 10000) == returns [v]

#guard runText (sumAt "i32") "@f" ["10"] == runText sumText "@sum" ["10"]
-- At `i1`, `%i` starts at `0`, which is at least `false` and `true`.
#guard loopRuns (sumAt "i1") [(["false"], "false"), (["true"], "false")]
-- The sum overflows when it passes the signed maximum, and `add nsw`
-- gives poison, which the loop carries to the end.
#guard loopRuns (sumAt "i7")
  [(["11"], "55"), (["12"], "poison"), (["63"], "poison"), (["2"], "1"), (["-64"], "0")]
#guard loopRuns (sumAt "i8") [(["16"], "120"), (["17"], "poison"), (["-128"], "0")]
#guard loopRuns (sumAt "i33") [(["100"], "4950"), (["-4294967296"], "0")]
#guard loopRuns (sumAt "i64") [(["100"], "4950"), (["-9223372036854775808"], "0")]

/-! # Factorial

`%n!`, counting `%n` down to `0` as an unsigned number, with `mul`, which
wraps: the result is `%n!` modulo `2^N`. -/

/-- `@f(%n: T) -> T`, the factorial of `%n` at the type `ty`. -/
def factAt (ty : String) : String :=
  body ("func @f(%n: " ++ ty ++ ") -> " ++ ty)
    ["^entry:", "  %one: " ++ ty ++ " = const " ++ lit ty 1 ++ " @0", "  br ^loop(%n, %one) @0",
     "^loop(%i: " ++ ty ++ ", %acc: " ++ ty ++ "):",
     "  %zero: " ++ ty ++ " = const " ++ lit ty 0 ++ " @0", "  %done: i1 = icmp eq %i, %zero @0",
     "  cond_br %done, ^exit(%acc), ^body @0", "^body:", "  %acc1: " ++ ty ++ " = mul %acc, %i @0",
     "  %i1: " ++ ty ++ " = sub %i, %one @0", "  br ^loop(%i1, %acc1) @0",
     "^exit(%r: " ++ ty ++ "):", "  ret %r @0"]

#guard loopRuns (factAt "i1") [(["true"], "true"), (["false"], "true")]
#guard loopRuns (factAt "i7") [(["0"], "1"), (["4"], "24"), (["5"], "-8"), (["6"], "-48")]
-- `-1` is `255`, and `255!` is a multiple of `256`.
#guard loopRuns (factAt "i8") [(["5"], "120"), (["6"], "-48"), (["-1"], "0")]
#guard loopRuns (factAt "i33") [(["12"], "479001600"), (["13"], "-2362913792")]
#guard loopRuns (factAt "i64")
  [(["20"], "2432902008176640000"), (["21"], "-4249290049419214848")]
#guard loopRuns (factAt "i128") [(["30"], "265252859812191058636308480000000"),
  (["34"], "-45049567881334322615755997788248211456")]

/-! # Greatest common divisor

Euclid's algorithm on `%a` and `%b` read as unsigned numbers, with `urem`.
Each trip round the loop passes `%y` and `%x urem %y` to `^loop`'s
arguments `%x` and `%y`: the value of one argument moves to the other. -/

/-- `@f(%a: T, %b: T) -> T`, the greatest common divisor of `%a` and `%b`
at the type `ty`. -/
def gcdAt (ty : String) : String :=
  body ("func @f(%a: " ++ ty ++ ", %b: " ++ ty ++ ") -> " ++ ty)
    ["^entry:", "  br ^loop(%a, %b) @0", "^loop(%x: " ++ ty ++ ", %y: " ++ ty ++ "):",
     "  %zero: " ++ ty ++ " = const " ++ lit ty 0 ++ " @0", "  %done: i1 = icmp eq %y, %zero @0",
     "  cond_br %done, ^exit(%x), ^body @0", "^body:", "  %r: " ++ ty ++ " = urem %x, %y @0",
     "  br ^loop(%y, %r) @0", "^exit(%g: " ++ ty ++ "):", "  ret %g @0"]

#guard loopRuns (gcdAt "i1") [(["true", "false"], "true"), (["false", "true"], "true"),
  (["true", "true"], "true"), (["false", "false"], "false")]
#guard loopRuns (gcdAt "i7") [(["60", "36"], "12"), (["-1", "63"], "1"), (["-64", "48"], "16")]
#guard loopRuns (gcdAt "i8") [(["48", "18"], "6"), (["-128", "96"], "32"), (["0", "7"], "7")]
#guard loopRuns (gcdAt "i33") [(["4294967295", "65535"], "65535"), (["-1", "21"], "7")]
#guard loopRuns (gcdAt "i64") [(["-1", "65535"], "65535"), (["9223372036854775807", "49"], "49"),
  (["-9223372036854775808", "1024"], "1024"), (["0", "0"], "0")]
-- Two consecutive Fibonacci numbers take the most trips for their size:
-- `182` here.
#guard loopRuns (gcdAt "i128") [(["-1", "3"], "3"),
  (["-170141183460469231731687303715884105728", "1024"], "1024"),
  (["127127879743834334146972278486287885163", "78569350599398894027251472817058687522"], "1")]

/-! # Block arguments that swap and rotate

A jump binds all of a block's arguments at once, to the values that the
successor passes, each read before any is bound. So a block that passes
its own arguments back to itself in another order permutes them. -/

/-- `@f(%a: T, %b: T, %n: i8) -> T, T`, which passes `^l`'s arguments
`%x` and `%y` back to it swapped, `%n` times. -/
def swapAt (ty : String) : String :=
  body ("func @f(%a: " ++ ty ++ ", %b: " ++ ty ++ ", %n: i8) -> " ++ ty ++ ", " ++ ty)
    ["^entry:", "  br ^l(%a, %b, %n) @0", "^l(%x: " ++ ty ++ ", %y: " ++ ty ++ ", %k: i8):",
     "  %zero: i8 = const 0 @0", "  %done: i1 = icmp eq %k, %zero @0",
     "  cond_br %done, ^exit(%x, %y), ^body @0", "^body:", "  %one: i8 = const 1 @0",
     "  %k1: i8 = sub %k, %one @0", "  br ^l(%y, %x, %k1) @0",
     "^exit(%p: " ++ ty ++ ", %q: " ++ ty ++ "):", "  ret %p, %q @0"]

/-- `@f(%a: T, %b: T, %c: T, %n: i8) -> T, T, T`, which passes `^l`'s
arguments `%x`, `%y` and `%z` back to it rotated, as `%y`, `%z` and `%x`,
`%n` times. -/
def rotateAt (ty : String) : String :=
  body ("func @f(%a: " ++ ty ++ ", %b: " ++ ty ++ ", %c: " ++ ty ++ ", %n: i8) -> " ++ ty ++
      ", " ++ ty ++ ", " ++ ty)
    ["^entry:", "  br ^l(%a, %b, %c, %n) @0",
     "^l(%x: " ++ ty ++ ", %y: " ++ ty ++ ", %z: " ++ ty ++ ", %k: i8):",
     "  %zero: i8 = const 0 @0", "  %done: i1 = icmp eq %k, %zero @0",
     "  cond_br %done, ^exit(%x, %y, %z), ^body @0", "^body:", "  %one: i8 = const 1 @0",
     "  %k1: i8 = sub %k, %one @0", "  br ^l(%y, %z, %x, %k1) @0",
     "^exit(%p: " ++ ty ++ ", %q: " ++ ty ++ ", %r: " ++ ty ++ "):", "  ret %p, %q, %r @0"]

/-- Each width with three of its values. -/
def rotateWidths : List (String × String × String × String) :=
  [("i1", "true", "false", "false"), ("i7", "-64", "63", "0"), ("i8", "-128", "127", "1"),
   ("i33", "-4294967296", "4294967295", "-1"),
   ("i64", "-9223372036854775808", "9223372036854775807", "0"),
   ("i128", "-170141183460469231731687303715884105728", "-1", "1")]

#guard rotateWidths.all fun (ty, a, b, _) =>
  valid (swapAt ty) &&
    runText (swapAt ty) "@f" [a, b, "0"] == returns [a, b] &&
    runText (swapAt ty) "@f" [a, b, "1"] == returns [b, a] &&
    runText (swapAt ty) "@f" [a, b, "2"] == returns [a, b] &&
    runText (swapAt ty) "@f" [a, b, "7"] == returns [b, a]
#guard rotateWidths.all fun (ty, a, b, c) =>
  valid (rotateAt ty) &&
    runText (rotateAt ty) "@f" [a, b, c, "0"] == returns [a, b, c] &&
    runText (rotateAt ty) "@f" [a, b, c, "1"] == returns [b, c, a] &&
    runText (rotateAt ty) "@f" [a, b, c, "2"] == returns [c, a, b] &&
    runText (rotateAt ty) "@f" [a, b, c, "3"] == returns [a, b, c] &&
    runText (rotateAt ty) "@f" [a, b, c, "4"] == returns [b, c, a]
-- A poison argument moves with its value, and stays poison.
#guard runIn inferInstance (swapAt "i8") ["poison", "3", "1"] == some (returns ["3", "poison"])
#guard runIn inferInstance (rotateAt "i64") ["1", "poison", "3", "2"] ==
  some (returns ["3", "1", "poison"])

/-! # Loops that never end

Each op takes one step of fuel, so a loop that never ends runs out of
fuel at every budget. `fir-ref run` sets the budget with `--fuel`. -/

/-- `@f()`, whose `^l` goes to itself. -/
def spin : String := body "func @f()" ["^entry:", "  br ^l @0", "^l:", "  br ^l @0"]

/-- `@f(%a: i8)`, whose `^l` passes `%i + 1` to itself, wrapping. -/
def countUp : String :=
  body "func @f(%a: i8)"
    ["^entry:", "  br ^l(%a) @0", "^l(%i: i8):", "  %one: i8 = const 1 @0",
     "  %j: i8 = add %i, %one @0", "  br ^l(%j) @0"]

#guard valid spin && valid countUp
#guard [0, 1, 2, 1000].all fun n => runText spin "@f" (fuel := n) == exhausted
#guard runText countUp "@f" ["0"] (fuel := 5000) == exhausted
#guard explore spin [] (fuel := 1000) == outcomes ["{\"kind\":\"fuel-exhausted\"}"] 0
#guard explore countUp ["127"] (fuel := 1000) == outcomes ["{\"kind\":\"fuel-exhausted\"}"] 0

end FirTest
