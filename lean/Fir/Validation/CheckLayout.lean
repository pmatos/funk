import Fir.Validation.CheckFuncs
import Fir.Validation.Layout

/-!
The check of a data layout follows its rule: the problems of each entry, in
order, then each memory that the layout declares more than once. The check
of a module's memories names, for each function and each item of a
dialect's kind whose types name a memory that the layout does not declare,
the first such memory (ADR-2026-11-12-1821).
-/

namespace Fir

/-- One problem, unless `c` holds. -/
def need (c : Prop) [Decidable c] (p : Problem) : List Problem := if c then [] else [p]

theorem need_eq_nil (c : Prop) [Decidable c] (p : Problem) : need c p = [] ↔ c := by
  unfold need
  split <;> simp_all

/-- The problems of an entry of the data layout. -/
def MemLayout.problems (e : MemLayout) : List Problem :=
  let at_ := "data layout: memory " ++ toString e.mem
  need (e.mem ≤ MemLayout.limit)
    { message := at_ ++ " is above " ++ toString MemLayout.limit } ++
  need (1 ≤ e.unit ∧ e.unit ≤ MemLayout.limit)
    { message := at_ ++ " has a unit of " ++ toString e.unit ++
      " bits: a unit has 1 to 16777215 bits" } ++
  need (1 ≤ e.pointer ∧ e.pointer ≤ MemLayout.limit)
    { message := at_ ++ " has pointers of " ++ toString e.pointer ++
      " bits: a pointer has 1 to 16777215 bits" } ++
  need (e.order = .little)
    { message := at_ ++ " is big-endian: M1 admits only little-endian memories" } ++
  need (∀ a ∈ e.align, isPowerOfTwo a ∧ a ≤ MemLayout.limit)
    { message := at_ ++ " aligns its pointers to " ++ toString (e.align.getD 0) ++
      " units: an alignment is a power of two no larger than 16777215" }

theorem MemLayout.problems_eq_nil (e : MemLayout) : e.problems = [] ↔ e.Valid := by
  simp only [MemLayout.problems, List.append_eq_nil_iff, need_eq_nil]
  exact ⟨fun ⟨⟨⟨⟨a, b⟩, c⟩, o⟩, l⟩ => ⟨a, b, c, o, l⟩, fun ⟨a, b, c, o, l⟩ => ⟨⟨⟨⟨a, b⟩, c⟩, o⟩, l⟩⟩

/-- The problems of a data layout: those of each entry, then each memory
it declares more than once. -/
def DataLayout.problems (l : DataLayout) : List Problem :=
  l.flatMap MemLayout.problems ++
  (repeats (l.map (·.mem))).map fun n =>
    { message := "data layout: memory " ++ toString n ++ " is declared more than once" }

theorem DataLayout.problems_eq_nil (l : DataLayout) : l.problems = [] ↔ l.Valid := by
  simp only [DataLayout.problems, List.append_eq_nil_iff, List.flatMap_eq_nil_iff,
    MemLayout.problems_eq_nil, List.map_eq_nil_iff, repeats_eq_nil]
  exact ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩⟩

instance DataLayout.decidableValid (l : DataLayout) : Decidable l.Valid :=
  decidable_of_iff _ l.problems_eq_nil

variable {d : Dialect} [DialectValidation d]

/-- The memories that types name and that the layout does not declare, in
order. -/
def DataLayout.missing (l : DataLayout) (ts : List d.Ty) : List Nat :=
  ts.filterMap fun t => (tyMemory t).filter fun n => !decide (l.Declares n)

theorem DataLayout.missing_eq_nil (l : DataLayout) (ts : List d.Ty) :
    l.missing ts = [] ↔ ∀ t ∈ ts, l.HasMemoryOf t := by
  simp only [DataLayout.missing, List.filterMap_eq_nil_iff, DataLayout.HasMemoryOf]
  refine forall_congr' fun t => imp_congr_right fun _ => ?_
  cases tyMemory t <;> simp [Option.filter]

/-- A problem for an item whose types name memories that the layout does
not declare: it names the first. -/
def memoryProblem (sym : Name) : List Nat → Option Problem
  | [] => none
  | n :: _ => some { message := "a type names memory " ++ toString n ++
      ", which the data layout does not declare", func := sym }

theorem memoryProblem_eq_none (sym : Name) (ns : List Nat) : memoryProblem sym ns = none ↔ ns = [] := by
  cases ns <;> simp [memoryProblem]

/-- The problems of the memories that a symbol table's types name: one for
each function, then one for each item of a dialect's kind, whose types name
a memory that the layout does not declare. -/
def SymbolTable.memoryProblems (l : DataLayout) (t : SymbolTable d) : List Problem :=
  t.funcs.filterMap (fun f => memoryProblem f.name (l.missing f.types)) ++
  t.dialectItems.filterMap (fun i => memoryProblem i.name (l.missing i.types))

theorem SymbolTable.memoryProblems_eq_nil (l : DataLayout) (t : SymbolTable d) :
    t.memoryProblems l = [] ↔ t.MemoriesIn l := by
  simp only [SymbolTable.memoryProblems, List.append_eq_nil_iff, List.filterMap_eq_nil_iff,
    memoryProblem_eq_none, DataLayout.missing_eq_nil]
  exact ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩⟩

end Fir
