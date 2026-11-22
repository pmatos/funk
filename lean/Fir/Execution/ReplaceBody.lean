import Fir.Execution.RefineRuns

/-!
# Replacing a body

Replacing the body of the function `@g` of a module gives the same module
with a new body in place of the body of `@g`. Every function keeps its
symbol, its parameters and its result types, and every other function
keeps its body. A caller reaches a callee only by its symbol
(ADR-2026-10-29-2012), so this replaces the callee `@g` for every caller
at once. The symbol table, and so the context of validation, stays the
same, and so do the dialect set, the data layout, the aggregates' layouts,
the globals and the external declarations: the new module is valid when the old one is and the new
function is valid in that context, with its types, and the types its ops
carry in their attributes, naming memories that the layout declares, with
the values its ops write as wide as their memories' units, and with the
integers its ops turn pointers into as wide as their memories' pointers,
in integral memories. The next
section uses this to replace a callee.
-/

namespace Fir

section

variable {d : Dialect}

/-- The function `f`, with the body `b` in place of its own when its symbol
is `s`. -/
abbrev Func.replaceBody (s : Name) (b : Region d) (f : Func d) : Func d :=
  { f with body := if f.name = s then b else f.body }

/-- An item, with the body `b` in place of its body when it is a function
whose symbol is `s`. A nested module is unchanged: its functions are in its
own symbol table. An item of a dialect's kind is unchanged too. -/
def Item.replaceBody (s : Name) (b : Region d) : Item d → Item d
  | .func f => .func (f.replaceBody s b)
  | i => i

/-- The module `M`, with the body `b` in place of the body of its function
whose symbol is `s`: every other part of it is unchanged. -/
def Module.replaceBody (M : Module d) (s : Name) (b : Region d) : Module d :=
  ⟨M.dialects, M.layout, M.items.map (Item.replaceBody s b), M.locs⟩

/-- The functions of `M` with a body replaced are those of `M`, each with
its body replaced when its symbol is `s`. -/
theorem Module.funcs_replaceBody (M : Module d) (s : Name) (b : Region d) :
    (M.replaceBody s b).funcs = M.funcs.map (Func.replaceBody s b) := by
  simp only [Module.replaceBody, Module.funcs, List.filterMap_map, List.map_filterMap]
  congr 1
  funext i
  cases i <;> rfl

/-- A function whose symbol is not `s` keeps its body. -/
theorem Func.replaceBody_of_ne {s : Name} {b : Region d} {f : Func d} (h : f.name ≠ s) :
    f.replaceBody s b = f := by
  simp [Func.replaceBody, h]

/-- The function `@s` gets the body `b`. -/
theorem Func.replaceBody_of_eq {s : Name} {b : Region d} {f : Func d} (h : f.name = s) :
    f.replaceBody s b = { f with body := b } := by
  simp [Func.replaceBody, h]

/-- The module with a body replaced finds the function it found, with its
body replaced when its symbol is `s`. -/
theorem Module.func?_replaceBody (M : Module d) (s : Name) (b : Region d) (x : Name) :
    (M.replaceBody s b).func? x = (M.func? x).map (Func.replaceBody s b) := by
  simp only [Module.func?, Module.funcs_replaceBody, List.find?_map]
  rfl

/-- In a module whose symbols are unique, a function of the module is the
one that its symbol finds. -/
theorem Module.func?_of_mem {M : Module d} (hnd : (M.funcs.map (·.name)).Nodup) {g : Func d}
    (hg : g ∈ M.funcs) : M.func? g.name = some g := by
  simp only [Module.func?]
  cases h : M.funcs.find? (·.name == g.name) with
  | none => exact absurd hg (by simpa using List.find?_eq_none.1 h g)
  | some k =>
    have hk := List.mem_of_find?_eq_some h
    have hn : k.name = g.name := by simpa using List.find?_some h
    rw [eq_of_nodup_map hnd hk hg hn]

/-- The function `@g` of a module whose symbols are unique is, with its new
body, the function of the module with that body that `@g`'s symbol names. -/
theorem Module.func?_replaceBody_self {M : Module d} (hnd : (M.funcs.map (·.name)).Nodup)
    {g : Func d} (hg : g ∈ M.funcs) (b : Region d) :
    (M.replaceBody g.name b).func? g.name = some (g.replaceBody g.name b) := by
  rw [Module.func?_replaceBody, Module.func?_of_mem hnd hg]
  rfl

/-- A symbol other than `s` names the same function in the module with a
body replaced as in the module. -/
theorem Module.func?_replaceBody_of_ne {M : Module d} {s x : Name} {b : Region d} (hx : x ≠ s) :
    (M.replaceBody s b).func? x = M.func? x := by
  rw [Module.func?_replaceBody]
  cases hk : M.func? x with
  | none => rfl
  | some k =>
    have hn : k.name = x := by simpa using List.find?_some hk
    simp only [Option.map_some, Func.replaceBody_of_ne (hn ▸ hx : k.name ≠ s)]

/-- Replacing a body keeps the symbol table: every function keeps its
symbol and its type. -/
theorem Module.symbols_replaceBody (M : Module d) (s : Name) (b : Region d) :
    (M.replaceBody s b).symbols = M.symbols := by
  funext x
  simp only [Module.symbols, Module.funcs_replaceBody, List.find?_map, Option.map_map]
  rfl

/-- Replacing a body keeps the aggregates' layouts of the module's own
table. -/
theorem Module.layouts_replaceBody (M : Module d) (s : Name) (b : Region d) :
    (M.replaceBody s b).table.layouts = M.table.layouts := by
  have h : (M.replaceBody s b).table.aggregates = M.table.aggregates := by
    simp only [SymbolTable.aggregates, Module.table, Module.replaceBody, List.filterMap_map]
    congr 1
    funext i
    cases i <;> rfl
  funext x
  simp only [SymbolTable.layouts, h]

/-- Replacing a body keeps the context in which the module's functions are
checked. -/
theorem Module.context_replaceBody (M : Module d) (s : Name) (b : Region d) :
    (M.replaceBody s b).context = M.context := by
  simp only [Module.context, Module.symbols_replaceBody, Module.layouts_replaceBody]
  rfl

/-- Replacing a body keeps every symbol of the module's own table. -/
theorem Item.name_replaceBody (s : Name) (b : Region d) (i : Item d) :
    (i.replaceBody s b).name = i.name := by
  cases i <;> rfl

/-- Replacing a body keeps the items of a dialect's kind of the module's own
table. -/
theorem Module.dialectItems_replaceBody (M : Module d) (s : Name) (b : Region d) :
    (M.replaceBody s b).table.dialectItems = M.table.dialectItems := by
  simp only [SymbolTable.dialectItems, Module.table, Module.replaceBody, List.filterMap_map]
  congr 1
  funext i
  cases i <;> rfl

/-- Replacing a body keeps the aggregates' layouts of the module's own
table. -/
theorem Module.aggregates_replaceBody (M : Module d) (s : Name) (b : Region d) :
    (M.replaceBody s b).table.aggregates = M.table.aggregates := by
  simp only [SymbolTable.aggregates, Module.table, Module.replaceBody, List.filterMap_map]
  congr 1
  funext i
  cases i <;> rfl

/-- Replacing a body keeps the globals of the module's own table. -/
theorem Module.globals_replaceBody (M : Module d) (s : Name) (b : Region d) :
    (M.replaceBody s b).table.globals = M.table.globals := by
  simp only [SymbolTable.globals, Module.table, Module.replaceBody, List.filterMap_map]
  congr 1
  funext i
  cases i <;> rfl

/-- Replacing a body keeps the external declarations of the module's own
table. -/
theorem Module.externs_replaceBody (M : Module d) (s : Name) (b : Region d) :
    (M.replaceBody s b).table.externs = M.table.externs := by
  simp only [SymbolTable.externs, Module.table, Module.replaceBody, List.filterMap_map]
  congr 1
  funext i
  cases i <;> rfl

/-- Replacing a body keeps the tables nested in the module's items: no
function holds one, and a nested module is unchanged. -/
theorem Item.tablesIn_replaceBody (s : Name) (b : Region d) :
    ∀ is : List (Item d), Item.tablesIn (is.map (Item.replaceBody s b)) = Item.tablesIn is
  | [] => rfl
  | i :: is => by
    rw [List.map_cons, Item.tablesIn, Item.tablesIn, Item.tablesIn_replaceBody s b is]
    cases i <;> rfl

variable [DialectSignature d] [DialectValidation d]

/-- A valid module with a body replaced is valid when its function `@s`
with the new body is valid in the module's context, which the replacement
keeps, and the module's layout declares the memories of its types and of
the types that its ops carry, gives units as wide as the values that its
ops write into them, and pointers as wide as the integers that its ops
turn them into, in integral memories. -/
theorem Module.valid_replaceBody {M : Module d} (hM : M.Valid) {s : Name} {b : Region d}
    (h : ∀ g ∈ M.funcs, g.name = s → ({ g with body := b } : Func d).Valid M.context)
    (hm : ∀ g ∈ M.funcs, g.name = s →
      ∀ ty ∈ ({ g with body := b } : Func d).types, M.layout.HasMemoryOf ty)
    (ha : ∀ g ∈ M.funcs, g.name = s →
      ∀ ty ∈ ({ g with body := b } : Func d).attrTypes, M.layout.HasMemoryOf ty)
    (hu : ∀ g ∈ M.funcs, g.name = s →
      ∀ q ∈ ({ g with body := b } : Func d).unitWidths, M.layout.HasUnits q)
    (hx : ∀ g ∈ M.funcs, g.name = s →
      ∀ q ∈ ({ g with body := b } : Func d).addrWidths, M.layout.HasAddrs q) :
    (M.replaceBody s b).Valid := by
  refine ⟨hM.locs, fun t ht => ?_, hM.layout, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  rotate_left
  · simp only [Module.tables, Module.replaceBody, Item.tablesIn_replaceBody, List.mem_cons] at ht
    rcases ht with rfl | ht
    · refine ⟨fun f hf => ?_, fun i hi => ?_, fun e he => ?_, fun f hf => ?_, fun f hf => ?_,
        fun f hf => ?_⟩
      · have hf' : f ∈ (M.replaceBody s b).funcs := hf
        rw [Module.funcs_replaceBody] at hf'
        obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf'
        by_cases hs : g.name = s
        · rw [Func.replaceBody_of_eq hs]
          exact hm g hg hs
        · rw [Func.replaceBody_of_ne hs]
          exact (hM.memories _ (List.mem_cons_self ..)).funcs g hg
      rotate_left 2
      · have hf' : f ∈ (M.replaceBody s b).funcs := hf
        rw [Module.funcs_replaceBody] at hf'
        obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf'
        by_cases hs : g.name = s
        · rw [Func.replaceBody_of_eq hs]
          exact ha g hg hs
        · rw [Func.replaceBody_of_ne hs]
          exact (hM.memories _ (List.mem_cons_self ..)).attrs g hg
      · have hf' : f ∈ (M.replaceBody s b).funcs := hf
        rw [Module.funcs_replaceBody] at hf'
        obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf'
        by_cases hs : g.name = s
        · rw [Func.replaceBody_of_eq hs]
          exact hu g hg hs
        · rw [Func.replaceBody_of_ne hs]
          exact (hM.memories _ (List.mem_cons_self ..)).units g hg
      · have hf' : f ∈ (M.replaceBody s b).funcs := hf
        rw [Module.funcs_replaceBody] at hf'
        obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf'
        by_cases hs : g.name = s
        · rw [Func.replaceBody_of_eq hs]
          exact hx g hg hs
        · rw [Func.replaceBody_of_ne hs]
          exact (hM.memories _ (List.mem_cons_self ..)).addrs g hg
      · have hi' : i ∈ (M.replaceBody s b).table.dialectItems := hi
        rw [Module.dialectItems_replaceBody] at hi'
        exact (hM.memories _ (List.mem_cons_self ..)).dialectItems i hi'
      · have he' : e ∈ (M.replaceBody s b).table.externs := he
        rw [Module.externs_replaceBody] at he'
        exact (hM.memories _ (List.mem_cons_self ..)).externs e he'
    · exact hM.memories t (List.mem_cons_of_mem _ ht)
  · simp only [Module.tables, Module.replaceBody, Item.tablesIn_replaceBody, List.mem_cons] at ht
    rcases ht with rfl | ht
    · intro a ha
      have ha' : a ∈ (M.replaceBody s b).table.aggregates := ha
      rw [Module.aggregates_replaceBody] at ha'
      exact hM.aggregates _ (List.mem_cons_self ..) a ha'
    · exact hM.aggregates t (List.mem_cons_of_mem _ ht)
  · simp only [Module.tables, Module.replaceBody, Item.tablesIn_replaceBody, List.mem_cons] at ht
    rcases ht with rfl | ht
    · intro g hg
      have hg' : g ∈ (M.replaceBody s b).table.globals := hg
      rw [Module.globals_replaceBody] at hg'
      show g.Valid M.layout (M.replaceBody s b).table.globals
      rw [Module.globals_replaceBody]
      exact hM.globals _ (List.mem_cons_self ..) g hg'
    · exact hM.globals t (List.mem_cons_of_mem _ ht)
  simp only [Module.tables, Module.replaceBody, Item.tablesIn_replaceBody, List.mem_cons] at ht
  rcases ht with rfl | ht
  · refine ⟨?_, fun f hf => ?_, fun i hi => ?_, fun e he => ?_, hM.dialectNames,
      hM.dialectsUnique⟩
    · change ((M.items.map (Item.replaceBody s b)).map Item.name).Nodup
      rw [List.map_map]
      have : Item.name ∘ Item.replaceBody s b = (Item.name : Item d → Name) :=
        funext (Item.name_replaceBody s b)
      rw [this]
      exact hM.table.symbolsUnique
    · have hc := Module.context_replaceBody M s b
      have hf' : f ∈ (M.replaceBody s b).funcs := hf
      change f.Valid (M.replaceBody s b).context
      rw [hc]
      rw [Module.funcs_replaceBody] at hf'
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf'
      by_cases hs : g.name = s
      · rw [Func.replaceBody_of_eq hs]
        exact h g hg hs
      · rw [Func.replaceBody_of_ne hs]
        exact hM.funcs g hg
    · have hi' : i ∈ (M.replaceBody s b).table.dialectItems := hi
      rw [Module.dialectItems_replaceBody] at hi'
      change i.Valid ⟨(M.replaceBody s b).symbols⟩
      rw [Module.symbols_replaceBody]
      exact hM.table.dialectItems i hi'
    · have he' : e ∈ (M.replaceBody s b).table.externs := he
      rw [Module.externs_replaceBody] at he'
      exact hM.table.externs e he'
  · exact hM.tables t (List.mem_cons_of_mem _ ht)

end

end Fir
