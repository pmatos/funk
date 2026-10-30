import Fir.Validation.CheckFuncs

/-!
The check of a module follows `Module.Valid`: its symbols, its location
table, then each function, in the context of the module. It builds the
module's symbol table and the set of its location references once, as hash
tables, and every function looks them up.

# The location table

The references of a table are in increasing order exactly when each one is
below the next, so the check compares each reference with the one after it.
-/

namespace Fir

variable {d : Dialect}

instance (l : Location) : Decidable l.WellFormed := by
  cases l <;> unfold Location.WellFormed <;> infer_instance

/-- Why a location that is not well formed is not. -/
def Location.malformed : Location → String
  | .range _ l₁ _ _ _ =>
    if 1 ≤ l₁ then "a range does not end before it starts" else "a range starts at line 1 or later"
  | .fused _ => "a fused location fuses at least two"
  | _ => "the location is not well formed"

/-- A problem about the entry of the location table with reference `r`. -/
def locProblem (r : LocRef) (s : String) : Problem :=
  { message := "location table: @" ++ toString r ++ " " ++ s }

/-- The problems of a location table. -/
def LocTable.problems (t : LocTable) : List Problem :=
  let keys := t.map (·.1)
  let held := Std.HashSet.ofList keys
  (keys.zip keys.tail).filterMap (fun (a, b) => if a < b then none else
    some (locProblem b ("comes after @" ++ toString a ++
      ": references are unique and in increasing order"))) ++
  t.flatMap fun (r, l) =>
    (if r < Location.limit ∧ ∀ n ∈ l.numbers, n < Location.limit then [] else
      [locProblem r "holds a reference, line or column of 2^32 or more"]) ++
    (if l.WellFormed then [] else [locProblem r ("is not well formed: " ++ l.malformed)]) ++
    l.refs.filterMap fun x => if x < r ∧ held.contains x then none else
      some (locProblem r ("refers to @" ++ toString x ++ ", which " ++
        if held.contains x then "does not come before it" else "the table does not hold"))

theorem pairwise_lt_iff_zip (l : List Nat) :
    l.Pairwise (· < ·) ↔ ∀ p ∈ l.zip l.tail, p.1 < p.2 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l =>
      have hz : (a :: b :: l).zip (a :: b :: l).tail = (a, b) :: (b :: l).zip (b :: l).tail := rfl
      rw [hz, List.pairwise_cons, ih]
      simp only [List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨⟨hab, _⟩, hr⟩
        exact ⟨hab, hr⟩
      · rintro ⟨hab, hr⟩
        refine ⟨⟨hab, fun c hc => Nat.lt_trans hab ?_⟩, hr⟩
        exact (List.pairwise_cons.mp (ih.mpr hr)).1 c hc

/-- The check of a location table decides `LocTable.Valid`. -/
theorem LocTable.problems_eq_nil (t : LocTable) : t.problems = [] ↔ t.Valid := by
  rw [LocTable.Valid, LocTable.InLimits, pairwise_lt_iff_zip]
  simp only [LocTable.problems, List.append_eq_nil_iff, List.filterMap_eq_nil_iff,
    ite_none_eq_none, List.flatMap_eq_nil_iff, ite_nil_eq_nil, Std.HashSet.contains_ofList,
    List.contains_iff_mem]
  constructor
  · rintro ⟨hp, he⟩
    exact ⟨hp, fun e h => (he e h).1.1, fun e h => ⟨(he e h).1.2, (he e h).2⟩⟩
  · rintro ⟨hp, hl, hw⟩
    exact ⟨hp, fun e h => ⟨⟨hl e h, (hw e h).1⟩, (hw e h).2⟩⟩

/-!
# Modules
-/

/-- The module's symbol table and location references, as hash tables. -/
def Module.lookup (m : Module d) : Lookup d :=
  let symbols := firsts (m.funcs.map fun f => (f.name, f.type))
  let held := Std.HashSet.ofList (m.locs.map (·.1))
  ⟨fun s => symbols[s]?, held.contains⟩

theorem Module.lookup_agrees (m : Module d) : m.lookup.Agrees m.context where
  symbols := by
    funext s
    simp [Module.lookup, Module.context, Module.symbols, getElem?_firsts, List.find?_map,
      Function.comp_def]
  hasLoc r := by simp [Module.lookup, Module.context]

variable [DialectSignature d] [DialectValidation d] [DecidableEq d.Ty]
  [DecidableDialectValidation d]

/-- The problems of a module: every rule of validation that it breaks. -/
def Module.problems (m : Module d) : List Problem :=
  let lk := m.lookup
  (repeats (m.funcs.map (·.name))).map (fun s =>
    { message := "the symbol " ++ Text.printSymbol s ++ " names more than one item", func := s }) ++
  m.locs.problems ++
  m.funcs.flatMap (·.problems lk)

/-- The validation check decides `Module.Valid`: a module has no problems
exactly when it is valid. -/
theorem Module.problems_eq_nil_iff (m : Module d) : m.problems = [] ↔ m.Valid := by
  simp only [Module.problems, List.append_eq_nil_iff, List.map_eq_nil_iff, repeats_eq_nil,
    LocTable.problems_eq_nil, List.flatMap_eq_nil_iff, Func.problems_eq_nil m.lookup_agrees]
  exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩

instance (m : Module d) : Decidable m.Valid := decidable_of_iff _ m.problems_eq_nil_iff

instance (ctx : ModuleContext d) (f : Func d) : Decidable (f.Valid ctx) :=
  decidable_of_iff _ (Func.problems_eq_nil (lk := ⟨ctx.symbols, fun r => decide (r ∈ ctx.locKeys)⟩)
    ⟨rfl, by simp⟩)

end Fir
