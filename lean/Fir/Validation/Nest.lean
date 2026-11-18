import Fir.Validation.Rules

/-!
# The module of a nested symbol table

A function of a nested module runs in its own symbol table: a call names a
function of that table, as validation checks it (ADR-2026-11-10-1510), and
the memories of its types are those of the data layout of the module that
holds it, at the top (ADR-2026-11-12-1821). So the module that a function
of a table runs in, `M.nest t`, has the table's dialect set and items, and
the layout and the location table of `M`. A module's own table gives the
module back (`Module.nest_table`). Each table of a valid module, nested at
any depth, gives a valid module (`Module.Valid.nest`), so every theorem
stated of the functions of a valid module holds of the functions of each of
its tables, a device module's kernels included.
-/

namespace Fir

variable {d : Dialect}

/-- The module that the functions of the symbol table `t` of `M` run in:
the table's dialect set and items, with `M`'s data layout and location
table. -/
def Module.nest (M : Module d) (t : SymbolTable d) : Module d :=
  { dialects := t.dialects, layout := M.layout, items := t.items, locs := M.locs }

/-- A module's own table gives the module back. -/
@[simp] theorem Module.nest_table (M : Module d) : M.nest M.table = M := rfl

@[simp] theorem Module.nest_funcs (M : Module d) (t : SymbolTable d) :
    (M.nest t).funcs = t.funcs := rfl

@[simp] theorem Module.nest_layout (M : Module d) (t : SymbolTable d) :
    (M.nest t).layout = M.layout := rfl

mutual
/-- A table nested in an item holds the tables nested in it among the
item's. -/
theorem Item.tables_closed : ∀ (i : Item d) {u : SymbolTable d}, u ∈ i.tables →
    ∀ v ∈ Item.tablesIn u.items, v ∈ i.tables
  | .func _, _, h, _, _ => nomatch h
  | .dialect _, _, h, _, _ => nomatch h
  | .module _ ds is, u, h, v, hv => by
    rw [Item.tables, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · exact .inr hv
    · exact .inr (Item.tablesIn_closed is h v hv)

/-- A table nested in a list of items holds the tables nested in it among
the list's. -/
theorem Item.tablesIn_closed : ∀ (is : List (Item d)) {u : SymbolTable d},
    u ∈ Item.tablesIn is → ∀ v ∈ Item.tablesIn u.items, v ∈ Item.tablesIn is
  | [], _, h, _, _ => nomatch h
  | i :: is, u, h, v, hv => by
    rw [Item.tablesIn, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl (Item.tables_closed i h v hv)
    · exact .inr (Item.tablesIn_closed is h v hv)
end

/-- The tables of the module of a table of `M` are tables of `M`. -/
theorem Module.tables_nest {M : Module d} {t : SymbolTable d} (ht : t ∈ M.tables) :
    ∀ v ∈ (M.nest t).tables, v ∈ M.tables := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact List.mem_cons_of_mem _ hv
  · exact List.mem_cons_of_mem _ (Item.tablesIn_closed _ ht v hv)

variable [DialectSignature d] [DialectValidation d]

/-- The module of each table of a valid module, nested at any depth, is
valid: its tables are tables of the module, and it has the module's
location table and data layout. -/
theorem Module.Valid.nest {M : Module d} (hM : M.Valid) {t : SymbolTable d} (ht : t ∈ M.tables) :
    (M.nest t).Valid :=
  ⟨hM.locs, fun v hv => hM.tables v (Module.tables_nest ht v hv), hM.layout,
    fun v hv => hM.memories v (Module.tables_nest ht v hv),
    fun v hv => hM.aggregates v (Module.tables_nest ht v hv)⟩

end Fir
