import Fir.Syntax.Module

/-!
The attributes of a function's signature. A function holds a list of
attributes for each of its first parameters, or results, and none for the
rest, with no empty list at the end, so a function that carries none holds
an empty list (ADR-2026-11-21-1307). The text writes the attributes of
every place, and decoding gives back that short form. An external
declaration holds them in the same way, and writes the header of a
function with no blocks.
-/

namespace Fir

variable {d : Dialect}

/-- The attributes of each of `n` places, a parameter's or a result's, from
a list that may leave out the empty lists at its end. -/
def padAttrs (n : Nat) (as : List (List Attr)) : List (List Attr) :=
  (List.range n).map (as.getD · [])

/-- A list of attributes for each place without the empty lists at its
end. -/
def trimAttrs (as : List (List Attr)) : List (List Attr) :=
  (as.reverse.dropWhile List.isEmpty).reverse

/-- A list of attributes for each of at most `n` places that leaves out the
empty lists at its end: the form a function holds. -/
def AttrsTrimmed (n : Nat) (as : List (List Attr)) : Prop :=
  as.length ≤ n ∧ ∀ a ∈ as.getLast?, a.isEmpty = false

instance (n : Nat) (as : List (List Attr)) : Decidable (AttrsTrimmed n as) :=
  match h : as.getLast? with
  | none => decidable_of_iff (as.length ≤ n) (by simp [AttrsTrimmed, h])
  | some a => decidable_of_iff (as.length ≤ n ∧ a.isEmpty = false) (by simp [AttrsTrimmed, h])

/-- The attributes of each of a function's parameters. -/
def Func.paramAttrsAll (f : Func d) : List (List Attr) := padAttrs f.params.length f.paramAttrs

/-- The attributes of each of a function's results. -/
def Func.resultAttrsAll (f : Func d) : List (List Attr) :=
  padAttrs f.results.length f.resultAttrs

/-- The function whose header an external declaration writes: its symbol
and its signature, with a body of no blocks. -/
def Extern.func (e : Extern d) : Func d :=
  ⟨e.name, e.params, e.results, ⟨none, []⟩, e.paramAttrs, e.resultAttrs, e.variadic⟩

end Fir
