import Fir.Validation.CheckFuncs

/-!
The check of an external declaration follows its rule premise by premise,
in its order (ADR-2026-11-09-1547): its parameters' names, then that each
is named once, its types, the form of its attributes, then the attributes
of each parameter and of each result.
-/

namespace Fir

variable {d : Dialect} [DialectValidation d] [DecidableDialectValidation d]

/-- A problem about the external declaration `e`. -/
def Extern.problem (e : Extern d) (message : String) : Problem := { message, func := e.name }

/-- The problems of an external declaration: every rule of a valid one that
it breaks. -/
def Extern.problems (e : Extern d) : List Problem :=
  e.params.filterMap (fun x => if isName x.1 then none else
    some (e.problem ("the parameter " ++ valueRef x.1 ++ " is not a name"))) ++
  (repeats (e.params.map (·.1))).map (fun x =>
    e.problem ("the declaration defines " ++ valueRef x ++ " more than once")) ++
  (if ∀ t ∈ e.types, validTy t then [] else [e.problem "a type of the declaration is not valid"]) ++
  (if AttrsTrimmed e.params.length e.paramAttrs ∧ AttrsTrimmed e.results.length e.resultAttrs
    then [] else [e.problem ("the declaration holds the attributes of its parameters or " ++
      "results in another form than the text reads")]) ++
  (e.params.zip e.func.paramAttrsAll).filterMap (fun x => if validSigAttrs x.1.2 x.2 then none else
    some (e.problem ("the attributes of parameter " ++ valueRef x.1.1 ++
      " are not ones its type allows"))) ++
  (e.results.zip e.func.resultAttrsAll).filterMap (fun x => if validSigAttrs x.1 x.2 then none else
    some (e.problem "the attributes of a result of the declaration are not ones its type allows"))

/-- The check of an external declaration decides `Extern.Valid`. -/
theorem Extern.problems_eq_nil_iff (e : Extern d) : e.problems = [] ↔ e.Valid := by
  simp only [Extern.problems, List.append_eq_nil_iff, ite_eq_left_iff, reduceCtorEq,
    imp_false, Decidable.not_not, List.filterMap_eq_nil_iff, List.map_eq_nil_iff,
    repeats_eq_nil]
  constructor
  · rintro ⟨⟨⟨⟨⟨a, b⟩, c⟩, ⟨g, h⟩⟩, i⟩, j⟩
    exact ⟨a, b, c, g, h, i, j⟩
  · rintro ⟨a, b, c, g, h, i, j⟩
    exact ⟨⟨⟨⟨⟨a, b⟩, c⟩, ⟨g, h⟩⟩, i⟩, j⟩

instance instDecidableExternValid (e : Extern d) : Decidable e.Valid :=
  decidable_of_iff _ e.problems_eq_nil_iff

end Fir
