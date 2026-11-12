import FirTest.DialectSet

/-!
Kinds of item that a dialect registers (ADR-2026-11-09-1543), on the shared
cases of `tests/dialects/item-kinds.cases`, which
`crates/funk-ir/tests/item_kinds.rs` reads too, so the two validators agree
on each of them.

The cases run in the sum of the core and the tagged dialect of
`FirTest.DialectSet`, which registers the kinds `toy.cell` and `toy.alias`.
Every reader decodes an item whose kind is a word of a dialect, whichever
dialect registers it; validation asks that a dialect of the sum register
the kind, that the item obey that dialect's rule, and that the table's
dialect set name the kind's dialect.
-/

namespace FirTest.ItemKindCases

open Fir FirTest.DialectSetCases

/-- The cases of the shared file on kinds of item. -/
def cases : List Case := read (include_str "../../tests/dialects/item-kinds.cases")

#guard cases.length == 16
#guard (cases.filter (·.accept)).length == 4
#guard (cases.filter (!·.holds)).map (·.name) == []

/-- The messages of the problems of a case's text, of validity and of its
dialect set. -/
def messages (name : String) : List String :=
  match cases.find? (·.name == name) with
  | some c =>
    match (Fir.parse c.text : Except ParseError (Module CoreTag)) with
    | .ok m => m.allProblems.map (·.message)
    | .error _ => []
  | none => []

-- The sum registers the tagged dialect's kinds, and the core registers none.
#guard itemKindNames (d := CoreTag) == ["toy.cell", "toy.alias"]
#guard itemKindNames (d := CoreDialect) == []

-- A kind that no dialect registers has no rule to break.
#guard messages "unregistered-kind" == ["no dialect registers the kind of item \"toy.box\""]
-- The rule of a kind is its dialect's.
#guard messages "cell-of-a-core-type" == ["the item breaks the rule of its kind \"toy.cell\""]
-- The kind's word names its dialect, which the table's set must name.
#guard messages "nested-cell-does-not-inherit-the-set" ==
  ["the item writes a word of the dialect toy, which the module's dialect set does not name"]
-- An item's symbol is a symbol of its table, as a function's is.
#guard messages "symbol-of-a-function" == ["the symbol @c names more than one item"]

-- A parse that rejects an item of a dialect's kind with a body, at its kind.
#guard match (Fir.parse "toy.cell @c() {\n^entry:\n  ret @0\n}\n\nlocs {\n}\n" :
    Except ParseError (Module CoreTag)) with
  | .error e => e.pos == ⟨1, 1⟩ && e.reason == "an item of a dialect's kind has an empty body"
  | .ok _ => false

end FirTest.ItemKindCases
