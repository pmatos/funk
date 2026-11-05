import Fir.Validation.CheckModule

/-!
`fir-ref validate` checks a module's location table with the spec's
`LocTable.problems`. Compiled in the spec, that check takes stack per entry
of the table and per reference of a location (#136):

* `keys.zip keys.tail` runs core's `List.zip`, which core compiles before
  its `@[csimp]` theorem that makes `List.zipWith` a loop, so it recurses
  once per entry;
* `∀ n ∈ l.numbers, n < Location.limit` is decided by core's
  `List.decidableBAll`, which recurses once per number of the location, so
  once per reference of a fused location.

`locTableProblems` is the same check, with `List.zipWith Prod.mk`, which
compiles to core's loop `List.zipWithTR`, and `List.all`, a loop, in their
place. Every other list function that it calls is a loop, or compiles to
one through core's `@[csimp]` theorems (`List.map`, `List.filterMap`,
`List.flatMap`, `++`), and `Std.HashSet.ofList` folds over its list.
`problems_eq_locTableProblems` proves the two equal and registers that with
`@[csimp]`. `FirRef.Validate` imports this module, so `moduleProblems`,
compiled there, calls `locTableProblems` (ADR-2026-10-30-1450).
-/

namespace FirRef

open Fir

/-- `LocTable.problems`, with no stack per entry of the table or per
reference of a location. -/
def locTableProblems (t : LocTable) : List Problem :=
  let keys := t.map (·.1)
  let held := Std.HashSet.ofList keys
  (List.zipWith Prod.mk keys keys.tail).filterMap (fun (a, b) => if a < b then none else
    some (locProblem b ("comes after @" ++ toString a ++
      ": references are unique and in increasing order"))) ++
  t.flatMap fun (r, l) =>
    (if r < Location.limit && l.numbers.all (· < Location.limit) then [] else
      [locProblem r "holds a reference, line or column of 2^32 or more"]) ++
    (if l.WellFormed then [] else [locProblem r ("is not well formed: " ++ l.malformed)]) ++
    l.refs.filterMap fun x => if x < r ∧ held.contains x then none else
      some (locProblem r ("refers to @" ++ toString x ++ ", which " ++
        if held.contains x then "does not come before it" else "the table does not hold"))

@[csimp] theorem problems_eq_locTableProblems : @LocTable.problems = @locTableProblems := by
  funext t
  simp only [LocTable.problems, locTableProblems, List.zip, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true]

end FirRef
