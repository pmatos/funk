import Fir.Validation.Layout

/-!
# The items a run gives each op

An op may name an item of its module by its symbol, as `call` names a
function. The run passes the module's items that ops read to every op's
rule, beside each memory's layout entry (the human's ruling of 2026-11-16
on #236, Q1 A). Today these are the aggregates' layouts of the table the
run's function belongs to, each field placed: its offset, and the units
from one of its elements to the next.

The record is the same for every dialect: its numbers count the units of a
memory of the module, and each field's step between elements is already
its type's units rounded up to its alignment, so no rule needs a dialect's
types to read it. A sum passes it to both of its sides unchanged.

Every obligation and guarantee over the semantics with memory holds for
every such record, with no hypothesis on it. So the items that later ops
name, such as the address of a function (#235) or of a global (#237), are
new fields of this record, which the run fills from its module, and the
statements of those obligations and guarantees stay as they are.

A run's record and validation read a table's layouts alike: each takes the
first layout with a symbol, so an op that validation accepts finds, in
every run, the layout it was checked against (`RunItems.ofTable_ref`).
-/

namespace Fir

/-- A field of an aggregate's layout as a run gives it to an op: its offset,
the units from one of its elements to the next, and its count when it is a
repeated field, all in units of the layout's memory. -/
structure FieldPlace where
  offset : Nat
  stride : Nat
  count : Option Nat

/-- An aggregate's layout as a run gives it to an op: its memory, size,
alignment and placed fields. -/
structure LayoutPlace where
  mem : Nat
  size : Nat
  align : Nat
  fields : List FieldPlace

/-- The items of a module that a run gives each op's rule: the layout of
each aggregate, by its symbol, if there is one. -/
structure RunItems where
  layout? : Name → Option LayoutPlace

/-- The items of a run that gives no item. -/
def RunItems.empty : RunItems := ⟨fun _ => none⟩

variable {d : Dialect} [DialectValidation d]

/-- A field placed in the memory `n` of a module whose data layout is `l`:
its offset and count, and the units of one value of its type rounded up to
its alignment, or no units when its type may not be a field. -/
def Field.place (l : DataLayout) (n : Nat) (f : Field d) : FieldPlace :=
  { offset := f.offset, count := f.count,
    stride := match f.shape l n with
      | some (u, a) => roundUp u a
      | none => 0 }

/-- An aggregate's layout placed in a module whose data layout is `l`. -/
def Aggregate.place (l : DataLayout) (a : Aggregate d) : LayoutPlace :=
  { mem := a.mem, size := a.size, align := a.align, fields := a.fields.map (Field.place l a.mem) }

/-- The items that a run of a function of the symbol table `t`, in a module
whose data layout is `l`, gives each op: the first aggregate's layout of
`t` with each symbol, placed. The layouts are placed once, not at each
lookup. -/
def RunItems.ofTable (l : DataLayout) (t : SymbolTable d) : RunItems :=
  let placed := t.aggregates.map fun a => (a.name, a.place l)
  ⟨fun s => placed.lookup s⟩

/-- The items that a run of a function of a module's own table gives each
op. -/
def Module.runItems (M : Module d) : RunItems := RunItems.ofTable M.layout M.table

/-- What the rule of an op sees of a placed layout: its memory, and the
count of each field, as validation sees an aggregate's layout. -/
def LayoutPlace.ref (p : LayoutPlace) : LayoutRef := ⟨p.mem, p.fields.map (·.count)⟩

/-- The run gives an op the layout that validation checks it against: the
first layout of the table with each symbol, placed, and seen as the rule
of an op sees it, is the table's layout of that symbol (`SymbolTable.layouts`).
So an op that validation accepts in a table finds its layout, of the same
memory and with the same fields, in each run of a function of the table. -/
theorem RunItems.ofTable_ref (l : DataLayout) (t : SymbolTable d) (s : Name) :
    ((RunItems.ofTable l t).layout? s).map LayoutPlace.ref = t.layouts s := by
  show (List.lookup s (t.aggregates.map fun a => (a.name, a.place l))).map LayoutPlace.ref =
    (t.aggregates.find? (·.name == s)).map Aggregate.ref
  induction t.aggregates with
  | nil => rfl
  | cons a as ih =>
    by_cases h : a.name = s
    · subst h
      simp [LayoutPlace.ref, Aggregate.ref, Aggregate.place, Field.place, Function.comp_def]
    · have h' : (s == a.name) = false := by simp; exact fun e => h e.symm
      have h'' : (a.name == s) = false := by simp; exact h
      simp only [List.map_cons, List.lookup, h', List.find?, h'']
      exact ih

end Fir
