import FirTest.Layout
import FirTest.DialectSet

/-!
Tests of external declarations (ADR-2026-11-09-1547): their text, which
reads back and prints as itself, and the headers that do not decode; and
the rules of a valid declaration: its markers, its types, the memories its
types name and the words of its types. Validation still rejects a call to
a declaration, which the run hands to the external-call rule
(`FirTest.ExtCall`); #239's next stage lets validation accept it.
`crates/funk-ir/tests/extern_decl.rs` checks the same texts, so the two
parsers agree on each and the two validators give the same problems for
each declaration; on the call they share only the verdict.
-/

namespace FirTest

open Fir

/-- A module whose one item is the declaration `extern @g(ps) rs`. -/
def externText (ps rs : String) : String := oneFunc ("extern @g(" ++ ps ++ ")" ++ rs ++ " {\n}\n")

/-! # The text -/

#guard roundTrips (externText "%fmt: ptr, ..." " -> i32")
#guard roundTrips (externText "..." "")
#guard roundTrips (externText "" "")
#guard roundTrips (externText "%c: i8 sext, %n: i32" " -> i8 zext")
#guard roundTrips (externText "%a: i16 zext, %b: f64, ..." " -> i32, i1 zext")
#guard roundTrips (oneFunc "extern @\"a b\"(%x: i64) -> ptr {\n}\n")
-- A nested module holds declarations of its own.
#guard roundTrips (oneFunc "module @dev() {\n  extern @g(%x: i8 sext) -> i8 {\n  }\n\n}\n")
-- A declaration beside a function.
#guard roundTrips (oneFunc ("extern @puts(%s: ptr) -> i32 {\n}\n\n" ++
  "func @f() {\n^e:\n  ret @0\n}\n"))

-- Headers that do not decode.
#guard rejectedAt (externText "" " zext") 1 13 "an extern with no results has no attributes"
#guard rejectedAt (oneFunc "extern @g() {\n^e:\n  ret @0\n}\n") 1 1 "an extern has an empty body"
#guard rejectedAt (oneFunc "extern @g() {\n  global @h() size(1) align(1) {\n  }\n\n}\n") 1 1
  "an extern has an empty body"
#guard rejectedAt (externText "%a: i32, %a: i32" "") 1 20 "value %a is defined twice"
#guard rejectedAt (externText "%a: i16777216" "") 1 15 "type i16777216 does not decode"
#guard rejectedAt (oneFunc "externs @g() {\n}\n") 1 1 "unknown item kind externs"
-- Only a `func` or an `extern` writes markers and `...`.
#guard rejectedAt (oneFunc "toy.cell @c(%a: i8 sext) {\n}\n") 1 20
  "only a func's or an extern's parameters carry attributes"

/-! # Validation -/

#guard valid (externText "%fmt: ptr, ..." " -> i32")
#guard valid (externText "%c: i8 sext, %n: i32" " -> i16 zext")
#guard valid (externText "%b: i1 zext" " -> i1 sext")
#guard checks (externText "%a: i32 sext" "")
  ["the attributes of parameter %a are not ones its type allows"]
#guard checks (externText "%a: ptr zext" "")
  ["the attributes of parameter %a are not ones its type allows"]
#guard checks (externText "" " -> f32 sext")
  ["the attributes of a result of the declaration are not ones its type allows"]
#guard checks (externText "%a: i8 sext zext" "")
  ["the attributes of parameter %a are not ones its type allows"]
#guard checks (externText "%a: i8 signext" "")
  ["the attributes of parameter %a are not ones its type allows"]
#guard checks (externText "%a: i0" "")
  ["a type of the declaration is not valid"]
#guard checks (externText "%p: ptr(1)" "")
  ["a type names memory 1, which the data layout does not declare"]
#guard valid ("layout memory(1, unit(8), pointer(64), little)\n\n" ++ externText "%p: ptr(1)" "")
#guard checks (oneFunc "extern @f() {\n}\n\nfunc @f() {\n^e:\n  ret @0\n}\n")
  ["the symbol @f names more than one item"]
-- A call to a declaration does not validate yet: validation accepts it with
-- #239's next stage, which gives the core's external call its event.
#guard checks (oneFunc ("extern @g(%a: i32) -> i32 {\n}\n\n" ++
    "func @f(%a: i32) -> i32 {\n^e:\n  %r: i32 = call @g %a @0\n  ret %r @0\n}\n"))
  ["the op refers to @g, which names no function", "the op breaks its dialect's own rule"]

end FirTest
