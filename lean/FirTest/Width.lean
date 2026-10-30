import FirTest.Modes

/-!
Tests of #17's width changes, `zext`, `sext` and `trunc`, on
`FirRef.runBytes`, which computes what `fir-ref run` writes and its exit
status: every valid pair of the widths 1, 7, 8, 16, 32, 33, 64 and 128, in
both directions, at the boundary values `0`, `1`, `-1`, the signed minimum
and the signed maximum of the operand's type, against a model in integer
arithmetic; the widest type, `i16777215`; a poison operand at every pair,
which gives poison; and choices that a width change passes on, in both
modes. The width changes are never UB, so no run here hits UB.
-/

namespace FirTest

open Fir FirRef

/-- `@f(%a: iM) -> iN`, which returns the width change `OP %a`. -/
def changeAt (op : String) (m n : Nat) : String :=
  body s!"func @f(%a: i{m}) -> i{n}" ["^e:", s!"  %r: i{n} = {op} %a @0", "  ret %r @0"]

/-- What `fir-ref run` reports on the width change `OP %a` from `iM` to
`iN`, with `%a` spelled `a`. -/
def change (op : String) (m n : Nat) (a : String) : RunReport :=
  runText (changeAt op m n) "@f" [a]

/-! # Boundary values, at every pair of widths

The model works on integers, not bit vectors: `zext` keeps the operand's
value read as unsigned, `sext` its value read as signed, and `trunc` its
value modulo `2^N`, read as signed. -/

/-- `x` modulo `2^N`, read as an `N`-bit two's-complement signed integer. -/
def signedAt (n : Nat) (x : Int) : Int :=
  let r := x % 2 ^ n
  if r < 2 ^ (n - 1) then r else r - 2 ^ n

/-- How `fir-ref` spells the value `x` of `iN`. -/
def spell (n : Nat) (x : Int) : String :=
  if n = 1 then (if x = 0 then "false" else "true") else toString x

/-- The boundary values of `iM`, as signed integers, each once: `0`, `1`,
`-1`, the signed minimum and the signed maximum. At `i1` they are `0` and
`-1`, written `false` and `true`. -/
def boundary (m : Nat) : List Int :=
  ([0, 1, -1, -(2 ^ (m - 1)), 2 ^ (m - 1) - 1].map (signedAt m)).eraseDups

/-- What the width change `OP` from `iM` to `iN` gives on the signed value
`x`, in integer arithmetic. -/
def model (op : String) (m n : Nat) (x : Int) : Int :=
  match op with
  | "zext" => x % 2 ^ m
  | "sext" => x
  | _ => signedAt n x

/-- The widths of these tests. -/
def widths : List Nat := [1, 7, 8, 16, 32, 33, 64, 128]

/-- Every valid width change among `widths`: `zext` and `sext` from each
width to each wider one, and `trunc` from each width to each narrower
one. -/
def pairs : List (String × Nat × Nat) :=
  widths.flatMap fun m => widths.flatMap fun n =>
    if m < n then [("zext", m, n), ("sext", m, n)] else if n < m then [("trunc", m, n)] else []

#guard pairs.length == 84
#guard (boundary 1, boundary 7) == ([0, -1], [0, 1, -1, -64, 63])
#guard pairs.all fun (op, m, n) => (boundary m).all fun x =>
  change op m n (spell m x) == returns [spell n (model op m n x)]

/-! # By hand

The same rules, value by value, where the top bit is set. -/

#guard change "zext" 1 8 "true" == returns ["1"]
#guard change "sext" 1 8 "true" == returns ["-1"]
#guard change "zext" 1 64 "false" == returns ["0"]
#guard change "zext" 8 32 "-1" == returns ["255"]
#guard change "sext" 8 32 "-1" == returns ["-1"]
#guard change "zext" 8 64 "-128" == returns ["128"]
#guard change "sext" 8 64 "-128" == returns ["-128"]
#guard change "zext" 7 33 "-64" == returns ["64"]
#guard change "sext" 7 8 "-64" == returns ["-64"]
#guard change "zext" 33 64 "-1" == returns ["8589934591"]
#guard change "sext" 33 64 "-4294967296" == returns ["-4294967296"]
#guard change "zext" 64 128 "-1" == returns ["18446744073709551615"]
#guard change "sext" 64 128 "-9223372036854775808" == returns ["-9223372036854775808"]
#guard change "trunc" 8 1 "2" == returns ["false"]
#guard change "trunc" 8 1 "-127" == returns ["true"]
#guard change "trunc" 32 8 "255" == returns ["-1"]
#guard change "trunc" 8 7 "64" == returns ["-64"]
#guard change "trunc" 33 7 "4294967295" == returns ["-1"]
#guard change "trunc" 64 33 "-9223372036854775808" == returns ["0"]
#guard change "trunc" 64 33 "9223372036854775807" == returns ["-1"]
#guard change "trunc" 128 64 "-170141183460469231731687303715884105728" == returns ["0"]
-- The widest type.
#guard change "zext" 64 16777215 "-1" == returns ["18446744073709551615"]
#guard change "sext" 1 16777215 "true" == returns ["-1"]
#guard change "trunc" 16777215 1 "-1" == returns ["true"]
#guard change "trunc" 16777215 64 "-9223372036854775809" == returns ["9223372036854775807"]

/-! # Poison

A poison operand gives poison, at every pair of widths. `fir-ref run`
takes no poison argument, so the first test gives one through the
interpreter as `fir-ref` runs it, and the next makes one with a broken
flag. -/

#guard pairs.all fun (op, m, n) =>
  runIn inferInstance (changeAt op m n) ["poison"] == some (returns ["poison"])

/-- `@f(%a: i8) -> i64, i1, i8`, which widens and narrows `add nsw %a, 1`:
poison at `127`. -/
def changesOfSum : String :=
  body "func @f(%a: i8) -> i64, i1, i8"
    ["^e:", "  %m: i8 = const 1 @0", "  %p: i8 = add nsw %a, %m @0", "  %z: i64 = zext %p @0",
     "  %t: i1 = trunc %p @0", "  %s: i64 = sext %p @0", "  %u: i8 = trunc %s @0",
     "  ret %z, %t, %u @0"]

#guard runText changesOfSum "@f" ["126"] == returns ["127", "true", "127"]
#guard runText changesOfSum "@f" ["-2"] == returns ["255", "true", "-1"]
#guard runText changesOfSum "@f" ["127"] == returns ["poison", "poison", "poison"]

/-! # Choices

A width change of a frozen poison passes on the bits that `freeze` chose.
Exhaustive mode tries the choices of `i2` from zero up as unsigned: `0`,
`1`, `-2` and `-1`. -/

/-- `@f(%a: i2) -> iN`, which returns `OP` of `freeze` of `add nsw %a, 1`:
a choice at `1`. -/
def frozenChange (op : String) (n : Nat) : String :=
  body s!"func @f(%a: i2) -> i{n}"
    ["^e:", "  %m: i2 = const 1 @0", "  %p: i2 = add nsw %a, %m @0", "  %f: i2 = freeze %p @0",
     s!"  %r: i{n} = {op} %f @0", "  ret %r @0"]

#guard explore (frozenChange "zext" 8) ["1"] ==
  outcomes [ret ["0"], ret ["1"], ret ["2"], ret ["3"]] 1
#guard explore (frozenChange "sext" 8) ["1"] ==
  outcomes [ret ["0"], ret ["1"], ret ["-2"], ret ["-1"]] 1
#guard explore (frozenChange "trunc" 1) ["1"] == outcomes [ret ["false"], ret ["true"]] 1
#guard explore (frozenChange "zext" 8) ["0"] == outcomes [ret ["1"]] 0
#guard runText (frozenChange "zext" 64) "@f" ["1"] (mode := .scripted ["-1"]) == returns ["3"] 1
#guard runText (frozenChange "sext" 64) "@f" ["1"] (mode := .scripted ["-2"]) == returns ["-2"] 1
#guard runText (frozenChange "trunc" 1) "@f" ["1"] (mode := .scripted ["-2"]) == returns ["false"] 1
-- A run that makes no choice, in exhaustive mode.
#guard explore (changeAt "sext" 8 64) ["-128"] == outcomes [ret ["-128"]] 0

-- The width changes have rules at every pair of widths, valid or not.
#guard [Core.Op.zext 1 2, .zext 8 8, .sext 64 1, .trunc 7 8, .trunc 16777215 1].all Core.Op.hasRules

/-! # The obligations' axioms -/

/-- info: 'Fir.Core.zext_propagatesPoison' depends on axioms: [propext] -/
#guard_msgs in #print axioms Fir.Core.zext_propagatesPoison

/-- info: 'Fir.Core.zext_returnsOnDefined' depends on axioms: [propext] -/
#guard_msgs in #print axioms Fir.Core.zext_returnsOnDefined

/-- info: 'Fir.Core.zext_total' depends on axioms: [propext] -/
#guard_msgs in #print axioms Fir.Core.zext_total

/-- info: 'Fir.Core.zext_monotone' depends on axioms: [propext] -/
#guard_msgs in #print axioms Fir.Core.zext_monotone

/-- info: 'Fir.Core.sext_propagatesPoison' depends on axioms: [propext] -/
#guard_msgs in #print axioms Fir.Core.sext_propagatesPoison

/-- info: 'Fir.Core.sext_returnsOnDefined' depends on axioms: [propext] -/
#guard_msgs in #print axioms Fir.Core.sext_returnsOnDefined

/-- info: 'Fir.Core.sext_total' depends on axioms: [propext] -/
#guard_msgs in #print axioms Fir.Core.sext_total

/-- info: 'Fir.Core.sext_monotone' depends on axioms: [propext] -/
#guard_msgs in #print axioms Fir.Core.sext_monotone

/-- info: 'Fir.Core.trunc_propagatesPoison' depends on axioms: [propext] -/
#guard_msgs in #print axioms Fir.Core.trunc_propagatesPoison

/-- info: 'Fir.Core.trunc_returnsOnDefined' depends on axioms: [propext] -/
#guard_msgs in #print axioms Fir.Core.trunc_returnsOnDefined

/-- info: 'Fir.Core.trunc_total' depends on axioms: [propext] -/
#guard_msgs in #print axioms Fir.Core.trunc_total

/-- info: 'Fir.Core.trunc_monotone' depends on axioms: [propext] -/
#guard_msgs in #print axioms Fir.Core.trunc_monotone

end FirTest
