import FirTest.Modes
import FirTest.ValidateOps

/-!
Tests of `call` on `FirRef.runBytes`, which computes what `fir-ref run`
writes (#20): direct recursion (factorial and Fibonacci), mutual recursion
(even and odd), the spec's example module, calls with no result, one and
several, and with many arguments of mixed widths, poison passed to a
callee and returned by one, UB in a callee, and recursion that runs out
of the fuel that a run sets. `fir-ref run` starts at any function of a
module, named as text names it, quoted when it is not a word. Every
module that these tests run is valid.
-/

namespace FirTest

open Fir FirRef

/-- A module of the functions `fs`, each a text that ends with a line
feed, and the location table. -/
def withFuncs (fs : List String) : String := oneFunc ("\n".intercalate fs)

/-- What `fir-ref run` reports on the function `func` of `t`, which must be
valid, at a budget of `10000` steps unless one is given. -/
def runValid (t func : String) (args : List String) (fuel : Nat := 10000)
    (mode : Mode := .scripted []) : RunReport :=
  if valid t then runText t func args fuel mode else fails 9 "the module is not valid"

/-! # Direct recursion

`@fact` multiplies `%n` by the factorial of `%n - 1`, down to `1`; the
product wraps at `i64`. `@fib` calls itself twice. -/

/-- `@fact`, the factorial at `i64`, as a function's text. -/
def factSource : String := "func @fact(%n: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %small: i1 = icmp sle %n, %one @0
  cond_br %small, ^base, ^rec @0
^base:
  %c: i64 = const 1 @0
  ret %c @0
^rec:
  %one1: i64 = const 1 @0
  %m: i64 = sub %n, %one1 @0
  %r: i64 = call @fact %m @0
  %p: i64 = mul %n, %r @0
  ret %p @0
}
"

/-- `@fact`'s module. -/
def factText : String := withFuncs [factSource]

#guard [("0", "1"), ("1", "1"), ("2", "2"), ("5", "120"), ("20", "2432902008176640000"),
    ("21", "-4249290049419214848"), ("-7", "1")].all fun (n, v) =>
  runValid factText "@fact" [n] == returns [v]
-- Each level above the last takes eight steps, the last five: `@fact` on
-- `5` takes 37 steps, its callees' included.
#guard runValid factText "@fact" ["5"] (fuel := 37) == returns ["120"]
#guard runValid factText "@fact" ["5"] (fuel := 36) == exhausted

/-- `@fib`, Fibonacci at `i32`: `%n` below `2` is its own value. -/
def fibText : String := withFuncs ["func @fib(%n: i32) -> i32 {
^entry:
  %two: i32 = const 2 @0
  %small: i1 = icmp slt %n, %two @0
  cond_br %small, ^base, ^rec @0
^base:
  ret %n @0
^rec:
  %one: i32 = const 1 @0
  %a: i32 = sub %n, %one @0
  %fa: i32 = call @fib %a @0
  %two1: i32 = const 2 @0
  %b: i32 = sub %n, %two1 @0
  %fb: i32 = call @fib %b @0
  %s: i32 = add %fa, %fb @0
  ret %s @0
}
"]

#guard [("0", "0"), ("1", "1"), ("2", "1"), ("3", "2"), ("10", "55"), ("15", "610")].all
  fun (n, v) => runValid fibText "@fib" [n] (fuel := 100000) == returns [v]

/-! # Mutual recursion

`@even` and `@odd` call each other on `%n - 1` down to `0`. On a negative
`%n` they count down for 2^32 calls, and run out of fuel first. -/

/-- `@even` or `@odd`, as `name`, which calls `other`, and returns `base`
at `0`. -/
def parity (name other base : String) : String :=
  "func @" ++ name ++ "(%n: i32) -> i1 {
^entry:
  %zero: i32 = const 0 @0
  %z: i1 = icmp eq %n, %zero @0
  cond_br %z, ^yes, ^no @0
^yes:
  %b: i1 = const " ++ base ++ " @0
  ret %b @0
^no:
  %one: i32 = const 1 @0
  %m: i32 = sub %n, %one @0
  %r: i1 = call @" ++ other ++ " %m @0
  ret %r @0
}
"

/-- `@even` and `@odd`. -/
def parityText : String := withFuncs [parity "even" "odd" "true", parity "odd" "even" "false"]

#guard [("0", "true"), ("1", "false"), ("7", "false"), ("10", "true")].all fun (n, v) =>
  runValid parityText "@even" [n] == returns [v]
#guard [("0", "false"), ("1", "true"), ("7", "true"), ("10", "false")].all fun (n, v) =>
  runValid parityText "@odd" [n] == returns [v]
#guard runValid parityText "@even" ["-1"] (fuel := 1000) == exhausted

/-! # The spec's example

`@sum10` calls `@sum` on `10`. It takes two steps of its own before the
call returns, `@sum`'s 65 and its `ret`: 68 in all. -/

#guard runValid Example.sumModule.print "@sum10" [] == returns ["45"]
#guard runValid Example.sumModule.print "@sum10" [] (fuel := 68) == returns ["45"]
#guard runValid Example.sumModule.print "@sum10" [] (fuel := 67) == exhausted
#guard runValid Example.sumModule.print "@sum" ["10"] == returns ["45"]

/-! # Results and arguments

A call has any number of results and of arguments, none included: no
result, one, or several, which the caller binds in order. -/

/-- The parameters of `@seven` and `@callseven`: seven, of mixed widths. -/
def sevenParams : String :=
  "(%a: i1, %b: i7, %c: i8, %d: i16, %e: i33, %f: i64, %g: i128)"

/-- `@seven` returns its seven arguments in reverse order. -/
def sevenText : String :=
  "func @seven" ++ sevenParams ++ " -> i128, i64, i33, i16, i8, i7, i1 {\n^e:\n" ++
    "  ret %g, %f, %e, %d, %c, %b, %a @0\n}\n"

/-- `@callseven` passes its seven arguments to `@seven`, and returns what
it returns in reverse order: its own arguments. -/
def callSevenText : String :=
  "func @callseven" ++ sevenParams ++ " -> i1, i7, i8, i16, i33, i64, i128 {\n^e:\n" ++
    "  %r1: i128, %r2: i64, %r3: i33, %r4: i16, %r5: i8, %r6: i7, %r7: i1 = " ++
    "call @seven %a, %b, %c, %d, %e, %f, %g @0\n" ++
    "  ret %r7, %r6, %r5, %r4, %r3, %r2, %r1 @0\n}\n"

/-- Functions with no result, one and several, and their callers. -/
def resultsText : String := withFuncs ["func @nothing() {
^e:
  ret @0
}
", "func @callnothing() {
^e:
  call @nothing @0
  ret @0
}
", "func @twice(%a: i8) -> i8 {
^e:
  %s: i8 = add %a, %a @0
  ret %s @0
}
", "func @calltwice(%a: i8) -> i8 {
^e:
  %r: i8 = call @twice %a @0
  ret %r @0
}
", "func @swap(%a: i8, %b: i16, %c: i1) -> i1, i16, i8 {
^e:
  ret %c, %b, %a @0
}
", "func @callswap(%a: i8, %b: i16, %c: i1) -> i8, i16, i1 {
^e:
  %x: i1, %y: i16, %z: i8 = call @swap %a, %b, %c @0
  ret %z, %y, %x @0
}
", sevenText, callSevenText]

#guard runValid resultsText "@callnothing" [] == returns []
#guard runValid resultsText "@calltwice" ["21"] == returns ["42"]
#guard runValid resultsText "@calltwice" ["-128"] == returns ["0"]
#guard runValid resultsText "@swap" ["1", "-2", "true"] == returns ["true", "-2", "1"]
#guard runValid resultsText "@callswap" ["1", "-2", "true"] == returns ["1", "-2", "true"]
#guard runValid resultsText "@callseven"
    ["true", "-64", "127", "-32768", "-4294967296", "9223372036854775807",
     "-170141183460469231731687303715884105728"] ==
  returns ["true", "-64", "127", "-32768", "-4294967296", "9223372036854775807",
    "-170141183460469231731687303715884105728"]

/-! # Poison through a call

A poison argument reaches the callee as poison, and a poison that the
callee returns is a poison result. A callee that ignores a poison
argument returns what it returns, and one that freezes it chooses. -/

/-- Callers that pass `add nsw %a, %a`, poison when it overflows, and
callees that return it, make it, ignore it or freeze it. -/
def poisonText : String := withFuncs ["func @id(%a: i8) -> i8 {
^e:
  ret %a @0
}
", "func @passes(%a: i8) -> i8 {
^e:
  %p: i8 = add nsw %a, %a @0
  %r: i8 = call @id %p @0
  ret %r @0
}
", "func @makes(%a: i8) -> i8 {
^e:
  %p: i8 = add nsw %a, %a @0
  ret %p @0
}
", "func @receives(%a: i8) -> i8, i8 {
^e:
  %r: i8 = call @makes %a @0
  %one: i8 = const 1 @0
  %s: i8 = add %r, %one @0
  ret %r, %s @0
}
", "func @five(%a: i8) -> i8 {
^e:
  %c: i8 = const 5 @0
  ret %c @0
}
", "func @ignored(%a: i8) -> i8 {
^e:
  %p: i8 = add nsw %a, %a @0
  %r: i8 = call @five %p @0
  ret %r @0
}
", "func @freezes(%a: i1) -> i1 {
^e:
  %f: i1 = freeze %a @0
  ret %f @0
}
", "func @frozen(%a: i1) -> i1 {
^e:
  %p: i1 = add nsw %a, %a @0
  %r: i1 = call @freezes %p @0
  ret %r @0
}
"]

#guard runValid poisonText "@passes" ["100"] == returns ["poison"]
#guard runValid poisonText "@passes" ["5"] == returns ["10"]
#guard runValid poisonText "@receives" ["64"] == returns ["poison", "poison"]
#guard runValid poisonText "@receives" ["3"] == returns ["6", "7"]
#guard runValid poisonText "@ignored" ["100"] == returns ["5"]
#guard runValid poisonText "@frozen" ["true"] (mode := .exhaustive 16) ==
  outcomes [ret ["false"], ret ["true"]] 1
#guard runValid poisonText "@frozen" ["true"] (mode := .scripted ["true"]) == returns ["true"] 1
#guard runValid poisonText "@frozen" ["false"] (mode := .exhaustive 16) ==
  outcomes [ret ["false"]] 0
-- `fir-ref run` takes no poison argument, but the spec's run does: the
-- first function, `@id`, returns it.
#guard runIn inferInstance poisonText ["poison"] == some (returns ["poison"])

/-! # UB in a callee

UB in a callee is UB of its caller, with the callee's reason, and nothing
after the call runs: here the `udiv` by zero that follows it would be UB
for another reason. -/

/-- `@div` divides, and `@divides` calls it, then divides by zero. -/
def divText : String := withFuncs ["func @div(%a: i8, %b: i8) -> i8 {
^e:
  %q: i8 = sdiv %a, %b @0
  ret %q @0
}
", "func @divides(%a: i8, %b: i8) -> i8 {
^e:
  %q: i8 = call @div %a, %b @0
  %zero: i8 = const 0 @0
  %r: i8 = udiv %q, %zero @0
  ret %r @0
}
", "func @calls(%a: i8, %b: i8) -> i8 {
^e:
  %q: i8 = call @div %a, %b @0
  ret %q @0
}
"]

/-- The report of a run that hits UB for `reason`. -/
def ubFor (reason : String) : RunReport :=
  { out := "{\"kind\":\"ub\",\"reason\":\"" ++ reason ++ "\",\"choices\":0}", status := 0 }

#guard runValid divText "@calls" ["7", "2"] == returns ["3"]
#guard runValid divText "@calls" ["7", "0"] == ubFor "sdiv by zero"
#guard runValid divText "@calls" ["-128", "-1"] == ubFor "sdiv of the signed minimum by -1"
#guard runValid divText "@divides" ["7", "0"] == ubFor "sdiv by zero"
#guard runValid divText "@divides" ["7", "2"] == ubFor "udiv by zero"

/-! # Recursion without end

A function that calls itself without end runs out of fuel at every
budget, in every mode: each call takes a step, and its callee runs on
the steps that are left. -/

/-- `@loop` calls itself on its argument. -/
def loopText : String := withFuncs ["func @loop(%a: i8) -> i8 {
^e:
  %r: i8 = call @loop %a @0
  ret %r @0
}
"]

#guard [0, 1, 2, 10, 100, 1000].all fun n =>
  runValid loopText "@loop" ["1"] (fuel := n) == exhausted
#guard runValid loopText "@loop" ["1"] (fuel := 100) (mode := .exhaustive 16) ==
  outcomes ["{\"kind\":\"fuel-exhausted\"}"] 0

/-! # Any function, named as text names it

`fir-ref run` runs any function of a module, not only the first, and
takes its symbol as text writes it: quoted when it is not a word, as in
`@"1"`, which `@1` is not. -/

/-- `@"1"` calls `@"a b"`, which adds one. -/
def quotedText : String := withFuncs ["func @\"1\"(%a: i8) -> i8 {
^e:
  %r: i8 = call @\"a b\" %a @0
  ret %r @0
}
", "func @\"a b\"(%a: i8) -> i8 {
^e:
  %one: i8 = const 1 @0
  %s: i8 = add %a, %one @0
  ret %s @0
}
"]

#guard runValid quotedText "@\"1\"" ["41"] == returns ["42"]
#guard runValid quotedText "@\"a b\"" ["41"] == returns ["42"]
#guard runValid quotedText "@1" ["41"] == fails 2 "fir-ref: t.fir has no function @1"
#guard runValid quotedText "@\"a\"" ["41"] == fails 2 "fir-ref: t.fir has no function @\"a\""
#guard runValid quotedText "@\"1\"" [] == fails 2 "fir-ref: @\"1\" takes 1 argument, not 0"

end FirTest
