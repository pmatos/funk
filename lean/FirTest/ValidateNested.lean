import FirTest.Validate

/-!
Tests of the validation check on nested modules (ADR-2026-11-10-1510): a
module is checked one symbol table at a time, its own and that of each
nested module, each with its own symbols and dialect set. A symbol names one
item of its table, function or nested module; an op refers only to a
function of its own table; and each nested module's functions are checked
as the top level's are. The must-reject texts of
`tests/fir/reject/validation-module.toml` check the same rules through both
tools.

The checks at the end run on modules nested 1,000,000 levels deep. This
module imports `FirRef.Fast` through `FirTest.Validate`, so the check lists
the tables with `FirRef.tablesIn`, which takes no stack per level; the
spec's `Item.tablesIn` overflows the stack there. `decide m.Valid` and
`FirRef.reportModule` reach the same check.
-/

namespace FirTest

open Fir Fir.Core

/-- A module of the items `is`, with the location table `@0 = unknown`. -/
def itemsModule (is : List (Item CoreDialect)) : Module CoreDialect := ⟨[], is, [(0, .unknown)]⟩

/-- A function `@name` whose one block calls `@callee` and returns. -/
def caller (name callee : Name) : Func CoreDialect :=
  ⟨name, [], [], ⟨none, [⟨"e", [], [op [] (.call callee [] []) [], op [] (.ret []) []]⟩]⟩⟩

/-! # One symbol table at a time -/

-- A module holds a table at each level of nesting, in order: its own, then
-- each nested module's, before the tables nested in it.
#guard ((itemsModule [.module "a" ["x"] [.module "b" [] []], .module "c" [] []]).tables.map
    (·.dialects)) == [[], ["x"], [], []]

-- The same symbol in two tables names two items, and a call resolves in its
-- own table.
#guard messages (itemsModule [.func (caller "f" "g"), .func (empty "g"),
  .module "dev" [] [.func (caller "g" "f"), .func (empty "f"), .module "dev" [] []]]) == []

-- A function and a module share a symbol of one table.
#guard messages (itemsModule [.func (empty "m"), .module "m" [] []]) ==
  ["the symbol @m names more than one item"]
#guard messages (itemsModule [.module "dev" [] [.module "m" [] [], .func (empty "m")]]) ==
  ["the symbol @m names more than one item"]

-- A call names a function of its own table: not one of a nested module's,
-- not one of its parent's, and not a module.
#guard messages (itemsModule [.func (caller "f" "g"), .module "dev" [] [.func (empty "g")]]) ==
  ["the op refers to @g, which names no function", "the op breaks its dialect's own rule"]
#guard messages (itemsModule [.func (empty "g"), .module "dev" [] [.func (caller "f" "g")]]) ==
  ["the op refers to @g, which names no function", "the op breaks its dialect's own rule"]
#guard messages (itemsModule [.func (caller "f" "m"), .module "m" [] []]) ==
  ["the op refers to @m, which names no function", "the op breaks its dialect's own rule"]

-- A nested module's functions and dialect set are checked too.
#guard messages (itemsModule [.module "dev" [] [.func (withBlocks [retBlock "e", retBlock "dead"])]])
  == ["block ^dead is not reachable from the entry"]
#guard messages (itemsModule [.module "dev" ["x y", "t", "t"] []]) ==
  ["the dialect set names \"x y\", which is not a word", "the dialect set names t more than once"]

/-! # At any depth -/

/-- Modules nested `n` levels deep, each holding the next, `@a`; the
innermost holds `inner`. -/
def deepModules (n : Nat) (inner : List (Item CoreDialect)) : Module CoreDialect :=
  itemsModule (Nat.repeat (fun is => [.module "a" [] is]) n inner)

#guard messages (deepModules 3 [.func (empty "a")]) == []
#guard messages (deepModules 3 [.func (empty "g"), .module "g" [] []]) ==
  ["the symbol @g names more than one item"]
#guard messages (deepModules 1000000 []) == []
#guard messages (deepModules 1000000 [.func (empty "g"), .module "g" [] []]) ==
  ["the symbol @g names more than one item"]
#guard decideValid (deepModules 1000000 [])
#guard FirRef.reportModule "t.fir" (deepModules 1000000 []) ==
  ("{\"file\":\"t.fir\",\"verdict\":\"accepted\",\"diagnostics\":[]}", 0)

/-! # The axioms of the proofs -/

/--
info: 'FirRef.tablesIn_eq_tablesIn' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms FirRef.tablesIn_eq_tablesIn

/--
info: 'Fir.validIsWellFormed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fir.validIsWellFormed

end FirTest
