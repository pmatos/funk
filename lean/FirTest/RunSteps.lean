import FirTest.Run

/-!
Tests of `fir-ref run` on long runs and deep calls (#47). `FirRef.runBytes`
calls the spec's `Core.scripted`, `Core.exhaustive` and `Core.sampled`,
and the `@[csimp]` theorems before it in `FirRef.Run` make it run
`FirRef.runScripted`, `FirRef.runExhaustive` and `FirRef.runSampled`, which
walk the states of `FirRef.Machine` and take no stack per step, per level
of calls or per choice. Below, each mode runs a loop that never ends and a
recursion that never ends for 1,000,000 steps, and a recursion 100,000
levels deep returns, with a choice at its bottom. The last checks pin the
axioms of the `@[csimp]` theorems to Lean's standard ones.
-/

namespace FirTest

open Fir FirRef

/-- A loop that never ends, `@spin`; a function that calls itself without
end, `@rec`; `@flip`, which freezes poison; and `@deep`, which calls
itself `%n` levels deep, calls `@flip` at the bottom, and returns what it
gives through every level. -/
def endless : String := oneFunc "func @spin() {
^e:
  br ^l @0
^l:
  br ^l @0
}

func @rec(%a: i8) -> i8 {
^e:
  %s: i8 = call @rec %a @0
  ret %s @0
}

func @flip() -> i1 {
^e:
  %t: i1 = const true @0
  %p: i1 = add nsw %t, %t @0
  %c: i1 = freeze %p @0
  ret %c @0
}

func @deep(%n: i32) -> i1 {
^e:
  %zero: i32 = const 0 @0
  %done: i1 = icmp sle %n, %zero @0
  cond_br %done, ^bottom, ^down @0
^bottom:
  %c: i1 = call @flip @0
  ret %c @0
^down:
  %one: i32 = const 1 @0
  %m: i32 = sub %n, %one @0
  %r: i1 = call @deep %m @0
  ret %r @0
}
"

/-- The report of sampled mode on a run that runs out of fuel and makes no
choice. -/
def exhaustedSampled : RunReport :=
  { out := "{\"kind\":\"fuel-exhausted\",\"choices\":0,\"sequence\":[]}", status := 0 }

/-- The report of exhaustive mode on a run whose one outcome is that it
runs out of fuel. -/
def exhaustedAll : RunReport :=
  { out := "{\"kind\":\"outcomes\",\"choices\":0,\"outcomes\":[{\"kind\":\"fuel-exhausted\"}]}",
    status := 0 }

/-! # A million steps, in each mode -/

#guard runText endless "@spin" (fuel := 1000000) == exhausted
#guard runText endless "@rec" ["1"] (fuel := 1000000) == exhausted
#guard runText endless "@spin" (fuel := 1000000) (mode := .exhaustive 16) == exhaustedAll
#guard runText endless "@rec" ["1"] (fuel := 1000000) (mode := .exhaustive 16) == exhaustedAll
#guard runText endless "@spin" (fuel := 1000000) (mode := .sampled 7) == exhaustedSampled
#guard runText endless "@rec" ["1"] (fuel := 1000000) (mode := .sampled 7) == exhaustedSampled

/-! # A choice 100,000 levels deep

`@deep 100000` takes 700,009 steps on each path: seven at each level
above the bottom, and nine at the bottom, `@flip`'s four included. -/

#guard runText endless "@deep" ["100000"] (mode := .exhaustive 1) ==
  { out := "{\"kind\":\"outcomes\",\"choices\":1,\"outcomes\":[" ++
      "{\"kind\":\"return\",\"values\":[\"false\"]},{\"kind\":\"return\",\"values\":[\"true\"]}]}",
    status := 0 }
#guard runText endless "@deep" ["100000"] (mode := .exhaustive 0) ==
  { out := "{\"kind\":\"choice-budget-exceeded\",\"budget\":0}", status := 0 }
#guard runText endless "@deep" ["100000"] (mode := .scripted ["true"]) == returns ["true"] 1
#guard runText endless "@deep" ["100000"] (fuel := 700009) (mode := .scripted ["false"]) ==
  returns ["false"] 1
#guard runText endless "@deep" ["100000"] (fuel := 700008) (mode := .scripted ["false"]) ==
  { out := "{\"kind\":\"fuel-exhausted\",\"choices\":1}", status := 0 }
#guard (runText endless "@deep" ["100000"] (mode := .sampled 3)).status == 0

/-! # The theorems' axioms -/

/--
info: 'FirRef.scripted_eq_runScripted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms FirRef.scripted_eq_runScripted

/--
info: 'FirRef.exhaustive_eq_runExhaustive' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms FirRef.exhaustive_eq_runExhaustive

/--
info: 'FirRef.sampled_eq_runSampled' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms FirRef.sampled_eq_runSampled

end FirTest
