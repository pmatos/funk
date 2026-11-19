import Fir.Validation.CheckLayout
import Fir.Validation.Global

/-!
The check of a global names each rule of a valid global that it breaks
(ADR-2026-11-09-1546): a number above the limit, a memory that the data
layout does not declare, an alignment that is not valid, the first unit of
each `units(…)` piece that does not fit its memory's unit, each address of
a symbol that names no global of the table, and an initializer that takes
more units than the global's size. Whether a unit fits is checked by a
shift, so a memory of wide units costs no power of two.
-/

namespace Fir

instance InitPiece.decidableInLimits (p : InitPiece) : Decidable p.InLimits := by
  cases p <;> unfold InitPiece.InLimits <;> infer_instance

/-- Whether a global's numbers are within the limit is decided piece by
piece with `List.all`, which takes no stack per piece. -/
instance Global.decidableInLimits (g : Global) : Decidable g.InLimits :=
  decidable_of_iff (g.mem ≤ Aggregate.limit ∧ g.size ≤ Aggregate.limit ∧
      g.align ≤ Aggregate.limit ∧ g.init.all fun p => decide p.InLimits)
    (by simp [Global.InLimits, List.all_eq_true])

/-- A unit is below `2^w` exactly when shifting it right by `w` leaves 0. -/
theorem lt_two_pow_iff_shiftRight (u w : Nat) : u < 2 ^ w ↔ u >>> w = 0 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff]
  simp

/-- A problem about the global `g`. -/
def Global.problem (g : Global) (message : String) : Problem := { message, func := g.name }

/-- The problems of a piece of the initializer of the global `g`, an item
of a table whose globals are `gs`, in a module whose data layout is `l`:
the first unit that does not fit, or an address of a symbol that names no
global of `gs`. -/
def InitPiece.problems (l : DataLayout) (gs : List Global) (g : Global) : InitPiece → List Problem
  | .units us =>
    match us.find? (fun u => u >>> (l.entry g.mem).unit != 0) with
    | some u => [g.problem ("the unit " ++ toString u ++ " of the initializer does not fit in " ++
        toString (l.entry g.mem).unit ++ " bits")]
    | none => []
  | .zeros _ => []
  | .addr s _ => need ((Global.named? gs s).isSome) (g.problem ("the initializer's address of @" ++
      s ++ " names no global of its table"))

theorem InitPiece.problems_eq_nil (l : DataLayout) (gs : List Global) (g : Global) (p : InitPiece) :
    p.problems l gs g = [] ↔ p.Fits l gs g.mem := by
  cases p with
  | units us =>
    simp only [InitPiece.problems, InitPiece.Fits, lt_two_pow_iff_shiftRight]
    cases hf : us.find? (fun u => u >>> (l.entry g.mem).unit != 0) with
    | some u =>
      have hm := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      simp only [reduceCtorEq, false_iff, Classical.not_forall]
      exact ⟨u, hm, by simpa using hp⟩
    | none =>
      simp only [true_iff]
      intro u hu
      simpa using List.find?_eq_none.mp hf u hu
  | zeros => simp [InitPiece.problems, InitPiece.Fits]
  | addr s k => simp [InitPiece.problems, InitPiece.Fits, need_eq_nil]

instance InitPiece.decidableFits (l : DataLayout) (gs : List Global) (g : Global) (p : InitPiece) :
    Decidable (p.Fits l gs g.mem) :=
  decidable_of_iff _ (p.problems_eq_nil l gs g)

/-- The problems of a global, an item of a table whose globals are `gs`, in
a module whose data layout is `l`: each rule of a valid global that it
breaks. -/
def Global.problems (l : DataLayout) (gs : List Global) (g : Global) : List Problem :=
  need g.InLimits (g.problem "a number of the global is above 2^64 - 1") ++
  need (l.Declares g.mem) (g.problem ("the global lives in memory " ++ toString g.mem ++
    ", which the data layout does not declare")) ++
  need (MemLayout.ValidAlign g.align) (g.problem ("the global is aligned to " ++
    toString g.align ++ " units: an alignment is a power of two no larger than 16777215")) ++
  g.init.flatMap (InitPiece.problems l gs g) ++
  need (g.initUnits l gs ≤ g.size) (g.problem ("the initializer takes " ++
    toString (g.initUnits l gs) ++ " units, more than the global's size, " ++ toString g.size))

/-- The check of a global decides `Global.Valid`. -/
theorem Global.problems_eq_nil (l : DataLayout) (gs : List Global) (g : Global) :
    g.problems l gs = [] ↔ g.Valid l gs := by
  simp only [Global.problems, List.append_eq_nil_iff, need_eq_nil, List.flatMap_eq_nil_iff,
    InitPiece.problems_eq_nil]
  exact ⟨fun ⟨⟨⟨⟨a, b⟩, c⟩, e⟩, f⟩ => ⟨a, b, c, e, f⟩, fun ⟨a, b, c, e, f⟩ => ⟨⟨⟨⟨a, b⟩, c⟩, e⟩, f⟩⟩

instance Global.decidableValid (l : DataLayout) (gs : List Global) (g : Global) :
    Decidable (g.Valid l gs) :=
  decidable_of_iff _ (g.problems_eq_nil l gs)

/-- The problems of the globals of a symbol table, each in its own table. -/
def SymbolTable.globalProblems {d : Dialect} (l : DataLayout) (t : SymbolTable d) : List Problem :=
  t.globals.flatMap (Global.problems l t.globals)

theorem SymbolTable.globalProblems_eq_nil {d : Dialect} (l : DataLayout) (t : SymbolTable d) :
    t.globalProblems l = [] ↔ ∀ g ∈ t.globals, g.Valid l t.globals := by
  simp [SymbolTable.globalProblems, List.flatMap_eq_nil_iff, Global.problems_eq_nil]

end Fir
