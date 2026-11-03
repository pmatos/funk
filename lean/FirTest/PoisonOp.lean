import FirTest.Div
import FirTest.Width

/-!
Tests of `poison`, the constant op of #122, on `FirRef.runBytes`, which
computes what `fir-ref run` writes: its text, which round-trips; its
result, the poison of its type, at every width of the corpus and at the
widest type; and what each kind of op does with that poison. Ops that
propagate poison give poison, `select` gives it only when it chooses it,
`freeze` chooses a value for it, and a branch on it or a division by it is
immediate UB. `fir-ref run` takes no `poison` argument, and these tests
need none: the op makes the poison (ADR-2026-11-03-1615).
-/

namespace FirTest

open Fir FirRef

/-- `@f() -> iN`, which returns `poison`. -/
def poisonOpAt (n : Nat) : String :=
  body s!"func @f() -> i{n}" ["^e:", s!"  %p: i{n} = poison @0", "  ret %p @0"]

/-- `@f(%a: iN) -> iN`, whose entry block makes `%p`, the poison of `iN`,
and then runs `lines`. -/
def withPoisonOp (n : Nat) (lines : List String) (params : String := s!"%a: i{n}")
    (results : String := s!"i{n}") : String :=
  body s!"func @f({params}) -> {results}" (["^e:", s!"  %p: i{n} = poison @0"] ++ lines)

/-! # Text

`poison` has no operands and no attributes, so its name comes right before
its location. Its text reads back and prints as itself, at every width. -/

#guard (widths ++ [16777215]).all fun n => roundTrips (poisonOpAt n)
#guard rejectedAt (func ["%p: i32 = poison %a @0", "ret %p @0"]) 3 13 "op poison does not decode"
#guard rejectedAt (func ["%p: i32 = poison 0 @0", "ret %p @0"]) 3 13 "op poison does not decode"
#guard rejectedAt (func ["%p: i32, %q: i32 = poison @0", "ret %p @0"]) 3 22
  "op poison does not decode"
#guard rejectedAt (func ["poison @0", "ret %a @0"]) 3 3 "op poison does not decode"

/-! # Its result

On every run, `poison` gives the poison of its type, and the run returns
it. It makes no choice. -/

#guard (widths ++ [16777215]).all fun n => runText (poisonOpAt n) "@f" == returns ["poison"]
#guard explore (poisonOpAt 8) [] == outcomes [ret ["poison"]] 0
#guard (Core.Op.poison 8).hasRules && (Core.Op.poison 0).hasRules
#guard Core.Op.poisonClass (.poison 1) == .propagates

/-! # What ops do with it

Two poisons are not two values: `icmp eq %p, %p` is poison, not `true`.
`select` gives the poison only on the arm it chooses. -/

/-- The argument `1` of `iN`, which is `true` at `i1`. -/
def oneOf (n : Nat) : String := if n = 1 then "true" else "1"

#guard widths.all fun n =>
  runText (withPoisonOp n [s!"  %s: i{n} = add %a, %p @0", "  ret %s @0"]) "@f" [oneOf n] ==
    returns ["poison"]
#guard runText (withPoisonOp 8 ["  %s: i64 = zext %p @0", "  ret %s @0"] (results := "i64"))
  "@f" ["1"] == returns ["poison"]
#guard runText (withPoisonOp 33 ["  %e: i1 = icmp eq %p, %p @0", "  ret %e @0"] (results := "i1"))
  "@f" ["1"] == returns ["poison"]
#guard runText (withPoisonOp 32 ["  %s: i32 = shl %a, %p @0", "  ret %s @0"]) "@f" ["1"] ==
  returns ["poison"]

/-- `@f(%c: i1, %a: iN) -> iN`, which returns `select %c, %p, %a`. -/
def selectPoisonOp (n : Nat) : String :=
  withPoisonOp n [s!"  %s: i{n} = select %c, %p, %a @0", "  ret %s @0"]
    (params := s!"%c: i1, %a: i{n}")

#guard widths.all fun n =>
  runText (selectPoisonOp n) "@f" ["true", oneOf n] == returns ["poison"] &&
    runText (selectPoisonOp n) "@f" ["false", oneOf n] == returns [oneOf n]

/-! # `freeze`, a branch and a division

`freeze` of the poison chooses a value, and every use of the frozen value
sees it, so `sub %f, %f` is `0`. A branch on the poison, and a division by
it, are immediate UB. -/

/-- `@f(%a: iN) -> iN`, which returns `freeze %p`. -/
def frozenPoisonOp (n : Nat) : String :=
  withPoisonOp n [s!"  %f: i{n} = freeze %p @0", "  ret %f @0"]

#guard explore (frozenPoisonOp 2) ["0"] ==
  outcomes [ret ["0"], ret ["1"], ret ["-2"], ret ["-1"]] 1
#guard runText (frozenPoisonOp 64) "@f" ["0"] (mode := .scripted ["-5"]) == returns ["-5"] 1
#guard explore (withPoisonOp 8 ["  %f: i8 = freeze %p @0", "  %d: i8 = sub %f, %f @0",
  "  ret %d @0"]) ["0"] == outcomes [ret ["0"]] 1
#guard runText (withPoisonOp 1 ["  cond_br %p, ^t, ^u @0", "^t:", "  ret %a @0", "^u:",
  "  ret %a @0"]) "@f" ["true"] == ubBy "cond_br on poison"
#guard runText (withPoisonOp 16 ["  %q: i16 = sdiv %a, %p @0", "  ret %q @0"]) "@f" ["1"] ==
  ubBy "sdiv by poison"

/-! # The obligations' axioms

The two obligations that name `Op.denote?` have the axioms of every core
rule it dispatches to, as `const`'s do. -/

/-- info: 'Fir.Core.poison_returnsOnDefined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.poison_returnsOnDefined

/-- info: 'Fir.Core.poison_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.poison_total

end FirTest
