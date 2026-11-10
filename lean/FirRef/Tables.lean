import Fir.Validation.Scope

/-!
`fir-ref validate` checks each symbol table of a module, its own and that
of each nested module, at any depth (ADR-2026-11-10-1510). The spec lists
them with `Item.tablesIn`, by mutual recursion, once per level of nesting.
Here, `tablesIn` lists the same tables with an explicit stack of lists of
items, in a loop whose recursive calls are tail calls, so it takes no stack
per level (ADR-2026-10-30-1549). `tablesIn_eq_tablesIn` proves the two
equal, and `@[csimp]` makes Lean compile every later call of
`Item.tablesIn` as a call of `tablesIn`, as `FirRef.allBlocks` does for
blocks (ADR-2026-10-30-1742).

The spec compiles `Module.tables` before that theorem exists, so its code
calls the spec's walk. `moduleTables` is its copy, compiled after it and
proved equal by `rfl`, and a second `@[csimp]` theorem makes `fir-ref`
call the copy.
-/

namespace FirRef

open Fir

variable {d : Dialect}

/-- Lists the symbol tables that a stack of lists of items holds, after
`acc`, which holds the tables listed so far, last first. -/
def tablesWalk (acc : List (SymbolTable d)) : List (List (Item d)) → List (SymbolTable d)
  | [] => acc.reverse
  | [] :: st => tablesWalk acc st
  | (.func _ :: is) :: st => tablesWalk acc (is :: st)
  | (.module _ ds js :: is) :: st => tablesWalk (⟨ds, js⟩ :: acc) (js :: is :: st)
termination_by st => sizeOf st
decreasing_by
  all_goals simp only [List.cons.sizeOf_spec, Item.func.sizeOf_spec, Item.module.sizeOf_spec]
  all_goals omega

/-- The loop lists the tables that its stack holds, after those it has
listed. -/
theorem tablesWalk_eq (acc : List (SymbolTable d)) (st : List (List (Item d))) :
    tablesWalk acc st = acc.reverse ++ st.flatMap Item.tablesIn := by
  fun_induction tablesWalk acc st <;> simp_all [Item.tablesIn, Item.tables]

/-- The symbol tables that a list of items holds, as `Item.tablesIn` lists
them, with no stack per level. -/
def tablesIn (is : List (Item d)) : List (SymbolTable d) := tablesWalk [] [is]

@[csimp] theorem tablesIn_eq_tablesIn : @Item.tablesIn = @tablesIn := by
  funext d is
  simp [tablesIn, tablesWalk_eq]

/-- `Module.tables`, compiled after `tablesIn_eq_tablesIn`. -/
def moduleTables (m : Module d) : List (SymbolTable d) := m.table :: Item.tablesIn m.items

@[csimp] theorem tables_eq_moduleTables : @Module.tables = @moduleTables := rfl

end FirRef
