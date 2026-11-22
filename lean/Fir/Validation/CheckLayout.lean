import Fir.Validation.CheckFuncs
import Fir.Validation.Layout

/-!
The check of a data layout follows its rule: the problems of each entry, in
order, then each memory that the layout declares more than once. The check
of a module's memories names, for each function, each item of a dialect's
kind and each external declaration whose types, or for a function the types that its ops carry
in their attributes, name a memory that the layout does not declare, the
first such memory (ADR-2026-11-12-1821), and for each function whose ops
write values into the units of a memory whose units are not as wide, the
first such memory. The check of an aggregate's layout
names each rule of a valid layout that it breaks, and each field that is not
placed (ADR-2026-11-16-1546).
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
  need (∀ a ∈ e.align, MemLayout.ValidAlign a)
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

/-- A problem for a function whose ops write values into the units of a
memory whose units are not as wide: it names the first such memory. -/
def unitsProblem (l : DataLayout) (sym : Name) (qs : List (Nat × Nat)) : Option Problem :=
  (qs.find? fun q => !decide (l.HasUnits q)).map fun q =>
    { message := "an op writes values of " ++ toString q.2 ++ " bits into memory " ++
        toString q.1 ++ ", whose units have " ++ toString (l.entry q.1).unit ++ " bits",
      func := sym }

theorem unitsProblem_eq_none (l : DataLayout) (sym : Name) (qs : List (Nat × Nat)) :
    unitsProblem l sym qs = none ↔ ∀ q ∈ qs, l.HasUnits q := by
  simp [unitsProblem, List.find?_eq_none]

/-- The problems of the memories that a symbol table's types name: one for
each function, then one for each item of a dialect's kind, then one for
each external declaration, whose types name a memory that the layout does
not declare, then one for each function
whose ops write values into units that are not as wide. A function's types
are those it states, then those its ops carry in their attributes. -/
def SymbolTable.memoryProblems (l : DataLayout) (t : SymbolTable d) : List Problem :=
  t.funcs.filterMap (fun f => memoryProblem f.name (l.missing (f.types ++ f.attrTypes))) ++
  t.dialectItems.filterMap (fun i => memoryProblem i.name (l.missing i.types)) ++
  t.externs.filterMap (fun e => memoryProblem e.name (l.missing e.types)) ++
  t.funcs.filterMap (fun f => unitsProblem l f.name f.unitWidths)

theorem SymbolTable.memoryProblems_eq_nil (l : DataLayout) (t : SymbolTable d) :
    t.memoryProblems l = [] ↔ t.MemoriesIn l := by
  simp only [SymbolTable.memoryProblems, List.append_eq_nil_iff, List.filterMap_eq_nil_iff,
    memoryProblem_eq_none, DataLayout.missing_eq_nil, List.mem_append, unitsProblem_eq_none]
  exact ⟨fun ⟨⟨⟨a, b⟩, e⟩, u⟩ => ⟨fun f hf ty h => a f hf ty (.inl h), b, e,
      fun f hf ty h => a f hf ty (.inr h), u⟩,
    fun ⟨a, b, e, c, u⟩ => ⟨⟨⟨fun f hf ty h => h.elim (a f hf ty) (c f hf ty), b⟩, e⟩, u⟩⟩

section
variable [DecidableDialectValidation d]

instance Aggregate.decidableInLimits (a : Aggregate d) : Decidable a.InLimits := by
  unfold Aggregate.InLimits
  infer_instance

/-- A problem about the aggregate's layout `a`. -/
def Aggregate.problem (a : Aggregate d) (message : String) : Problem := { message, func := a.name }

/-- The problems of a field of the aggregate's layout `a`: a type that may
not be a field, or else each rule of a placed field that it breaks. -/
def Field.problems (l : DataLayout) (a : Aggregate d) (f : Field d) : List Problem :=
  let at_ := "the field at offset " ++ toString f.offset
  match f.shape l a.mem with
  | none => [a.problem (at_ ++ " has a type that may not be a field: an integer, a float or a pointer")]
  | some (u, al) =>
    need (al ∣ f.offset) (a.problem (at_ ++ " is not a multiple of its type's alignment, " ++
      toString al)) ++
    need (al ≤ a.align) (a.problem (at_ ++ " has a type aligned to " ++ toString al ++
      " units, more than the layout's " ++ toString a.align)) ++
    need (f.offset + f.extent u al ≤ a.size) (a.problem (at_ ++ " ends past the layout's size, " ++
      toString a.size))

omit [DecidableDialectValidation d] in
theorem Field.problems_eq_nil (l : DataLayout) (a : Aggregate d) (f : Field d) :
    f.problems l a = [] ↔ f.Placed l a.mem a.size a.align := by
  unfold Field.problems Field.Placed
  cases f.shape l a.mem with
  | none => simp
  | some s =>
    obtain ⟨u, al⟩ := s
    simp only [List.append_eq_nil_iff, need_eq_nil, and_assoc]

/-- The problems of an aggregate's layout in a module whose data layout is
`l`: each rule of a valid layout that it breaks, with one problem for each
field that is not placed. -/
def Aggregate.problems (l : DataLayout) (a : Aggregate d) : List Problem :=
  need a.InLimits (a.problem "a number of the layout is above 2^64 - 1") ++
  need (l.Declares a.mem) (a.problem ("the layout describes memory " ++ toString a.mem ++
    ", which the data layout does not declare")) ++
  need (MemLayout.ValidAlign a.align) (a.problem ("the layout is aligned to " ++
    toString a.align ++ " units: an alignment is a power of two no larger than 16777215")) ++
  need (∀ t ∈ a.types, validTy t) (a.problem "a type of the layout is not valid") ++
  (memoryProblem a.name (l.missing a.types)).toList ++
  a.fields.flatMap (Field.problems l a) ++
  need (a.fields.Pairwise (Field.Apart l a.mem)) (a.problem "two fields of the layout share a unit")

/-- The check of an aggregate's layout decides `Aggregate.Valid`. -/
theorem Aggregate.problems_eq_nil (l : DataLayout) (a : Aggregate d) :
    a.problems l = [] ↔ a.Valid l := by
  have hm : (memoryProblem a.name (l.missing a.types)).toList = [] ↔
      ∀ t ∈ a.types, l.HasMemoryOf t := by
    rw [← DataLayout.missing_eq_nil, ← memoryProblem_eq_none a.name]
    cases memoryProblem a.name (l.missing a.types) <;> simp
  simp only [Aggregate.problems, List.append_eq_nil_iff, need_eq_nil, hm,
    List.flatMap_eq_nil_iff, Field.problems_eq_nil]
  exact ⟨fun ⟨⟨⟨⟨⟨⟨z, a⟩, b⟩, c⟩, e⟩, f⟩, g⟩ => ⟨z, a, b, c, e, f, g⟩,
    fun ⟨z, a, b, c, e, f, g⟩ => ⟨⟨⟨⟨⟨⟨z, a⟩, b⟩, c⟩, e⟩, f⟩, g⟩⟩

instance Aggregate.decidableValid (l : DataLayout) (a : Aggregate d) : Decidable (a.Valid l) :=
  decidable_of_iff _ (a.problems_eq_nil l)

end

end Fir
