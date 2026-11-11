import Fir.Validation.CheckFuncs

/-!
The check of a module follows the rule of a valid module: its location
table, then each of its symbol tables, its own and that of each nested
module: the symbols of its items, each function, in the context of the
table, each item of a dialect's kind, then its dialect set. It builds the
set of the module's location references once, and each table's symbols
once, as hash tables, and every function looks them up.

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
# Items of a dialect's kind

An item of a dialect's kind is checked against the general rules of such an
item, then the dialect's rule for it. Whether its attributes can be written
is decided attribute by attribute.
-/

mutual
/-- Whether an attribute can be written: `Attr.Writable`, as a test. -/
def Attr.writable : Attr → Bool
  | .word w => isWord w
  | .int _ | .str _ | .sym _ => true
  | .app h args => isWord h && Attr.allWritable args
  | .float l => l.valid

/-- Whether every attribute of a list can be written. -/
def Attr.allWritable : List Attr → Bool
  | [] => true
  | a :: as => a.writable && Attr.allWritable as
end

mutual
theorem Attr.writable_iff : ∀ a : Attr, a.writable = true ↔ a.Writable
  | .word _ | .int _ | .str _ | .sym _ | .float _ => by simp [Attr.writable, Attr.Writable]
  | .app _ args => by simp [Attr.writable, Attr.Writable, Attr.allWritable_iff args]

theorem Attr.allWritable_iff : ∀ as : List Attr, Attr.allWritable as = true ↔ Attr.AllWritable as
  | [] => by simp [Attr.allWritable, Attr.AllWritable]
  | a :: as => by
    simp [Attr.allWritable, Attr.AllWritable, Attr.writable_iff a, Attr.allWritable_iff as]
end

instance instDecidableAllWritable (as : List Attr) : Decidable (Attr.AllWritable as) :=
  decidable_of_iff _ (Attr.allWritable_iff as)

section
variable [DialectValidation d] [DecidableDialectValidation d]

/-- A problem about the item `i` of a dialect's kind. -/
def DialectItem.problem (i : DialectItem d) (message : String) : Problem :=
  { message, func := i.name }

/-- The problem of an item whose kind no dialect registers, or the problem
of an item that breaks the rule of its kind. A kind that no dialect
registers has no rule to break. -/
def DialectItem.kindProblems (ctx : FuncContext d) (i : DialectItem d) : List Problem :=
  if i.kind ∈ itemKindNames (d := d) then
    if validItem (DialectView.id d) ctx i then [] else
      [i.problem ("the item breaks the rule of its kind " ++ Text.quote i.kind)]
  else [i.problem ("no dialect registers the kind of item " ++ Text.quote i.kind)]

theorem DialectItem.kindProblems_eq_nil_iff (ctx : FuncContext d) (i : DialectItem d) :
    i.kindProblems ctx = [] ↔ i.kind ∈ itemKindNames (d := d) ∧ validItem (DialectView.id d) ctx i := by
  unfold DialectItem.kindProblems
  split
  · split <;> simp_all
  · simp_all

/-- The problems of an item of a dialect's kind, with the symbols of its
table: every rule of a valid item that it breaks. -/
def DialectItem.problems (ctx : FuncContext d) (i : DialectItem d) : List Problem :=
  (if isDialectWord i.kind then [] else
    [i.problem ("the kind " ++ Text.quote i.kind ++ " is not a word of a dialect")]) ++
  i.params.filterMap (fun x => if isName x.1 then none else
    some (i.problem ("the parameter " ++ valueRef x.1 ++ " is not a name"))) ++
  (repeats (i.params.map (·.1))).map (fun x =>
    i.problem ("the item defines " ++ valueRef x ++ " more than once")) ++
  (if ∀ t ∈ i.types, validTy t then [] else [i.problem "a type of the item is not valid"]) ++
  (if Attr.allWritable i.attrs then [] else
    [i.problem "an attribute of the item cannot be written"]) ++
  i.kindProblems ctx

/-- The check of an item of a dialect's kind decides `DialectItem.Valid`. -/
theorem DialectItem.problems_eq_nil_iff (ctx : FuncContext d) (i : DialectItem d) :
    i.problems ctx = [] ↔ i.Valid ctx := by
  simp only [DialectItem.problems, List.append_eq_nil_iff, ite_eq_left_iff, reduceCtorEq,
    imp_false, Decidable.not_not, List.filterMap_eq_nil_iff, List.map_eq_nil_iff,
    repeats_eq_nil, Attr.allWritable_iff, DialectItem.kindProblems_eq_nil_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨a, c⟩, e⟩, f⟩, g⟩, b, h⟩
    exact ⟨a, b, c, e, f, g, h⟩
  · rintro ⟨a, b, c, e, f, g, h⟩
    exact ⟨⟨⟨⟨⟨a, c⟩, e⟩, f⟩, g⟩, b, h⟩

instance instDecidableDialectItemValid (ctx : FuncContext d) (i : DialectItem d) :
    Decidable (i.Valid ctx) :=
  decidable_of_iff _ (i.problems_eq_nil_iff ctx)

end

/-!
# Modules

A module is checked one symbol table at a time: its own, then that of each
nested module, at any depth, each with its own symbols and dialect set, and
all with the module's one set of location references.
-/

/-- The lookup of a symbol table: its symbols, as a hash table, and the
references `held` of the module's location table. -/
def SymbolTable.lookup (held : Std.HashSet LocRef) (t : SymbolTable d) : Lookup d :=
  let symbols := firsts (t.funcs.map fun f => (f.name, f.type))
  ⟨fun s => symbols[s]?, held.contains⟩

theorem SymbolTable.lookup_agrees (keys : List LocRef) (t : SymbolTable d) :
    (t.lookup (Std.HashSet.ofList keys)).Agrees (t.context keys) where
  symbols := by
    funext s
    simp [SymbolTable.lookup, SymbolTable.context, SymbolTable.symbols, getElem?_firsts,
      List.find?_map, Function.comp_def]
  hasLoc r := by simp [SymbolTable.lookup, SymbolTable.context]

variable [DialectSignature d] [DialectValidation d] [DecidableEq d.Ty]
  [DecidableDialectValidation d]

/-- The problems of a symbol table, with the references `held` of the
module's location table: every rule of a valid table that it breaks. -/
def SymbolTable.problems (held : Std.HashSet LocRef) (t : SymbolTable d) : List Problem :=
  let lk := t.lookup held
  (repeats (t.items.map Item.name)).map (fun s =>
    { message := "the symbol " ++ Text.printSymbol s ++ " names more than one item", func := s }) ++
  t.funcs.flatMap (·.problems lk) ++
  t.dialectItems.flatMap (·.problems ⟨lk.symbols⟩) ++
  t.dialects.filterMap (fun x => if isWord x then none else
    some { message := "the dialect set names " ++ Text.quote x ++ ", which is not a word" }) ++
  (repeats t.dialects).map fun x => { message := "the dialect set names " ++ x ++ " more than once" }

/-- The check of a symbol table decides `SymbolTable.Valid`. -/
theorem SymbolTable.problems_eq_nil_iff (keys : List LocRef) (t : SymbolTable d) :
    t.problems (Std.HashSet.ofList keys) = [] ↔ t.Valid keys := by
  simp only [SymbolTable.problems, List.append_eq_nil_iff, List.map_eq_nil_iff, repeats_eq_nil,
    List.flatMap_eq_nil_iff, Func.problems_eq_nil (t.lookup_agrees keys),
    DialectItem.problems_eq_nil_iff, (t.lookup_agrees keys).symbols,
    List.filterMap_eq_nil_iff, ite_none_eq_none]
  exact ⟨fun ⟨⟨⟨⟨a, b⟩, i⟩, c⟩, e⟩ => ⟨a, b, i, c, e⟩,
    fun ⟨a, b, i, c, e⟩ => ⟨⟨⟨⟨a, b⟩, i⟩, c⟩, e⟩⟩

/-- The problems of a module: those of its location table, then those of
each of its symbol tables, in order. -/
def Module.problems (m : Module d) : List Problem :=
  let held := Std.HashSet.ofList (m.locs.map (·.1))
  m.locs.problems ++ m.tables.flatMap (·.problems held)

/-- The validation check decides `Module.Valid`: a module has no problems
exactly when it is valid. -/
theorem Module.problems_eq_nil_iff (m : Module d) : m.problems = [] ↔ m.Valid := by
  simp only [Module.problems, List.append_eq_nil_iff, LocTable.problems_eq_nil,
    List.flatMap_eq_nil_iff, SymbolTable.problems_eq_nil_iff]
  exact ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩⟩

instance (m : Module d) : Decidable m.Valid := decidable_of_iff _ m.problems_eq_nil_iff

instance (ctx : ModuleContext d) (f : Func d) : Decidable (f.Valid ctx) :=
  decidable_of_iff _ (Func.problems_eq_nil (lk := ⟨ctx.symbols, fun r => decide (r ∈ ctx.locKeys)⟩)
    ⟨rfl, by simp⟩)

end Fir
