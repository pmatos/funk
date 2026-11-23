import Fir.Validation.Global
import Fir.Memory.Policy
import Fir.Memory.Resolver
import Fir.Memory.Encode

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

The record also carries the run's address policy for each memory, by the
memory's number in the data layout: which address the run proposes for an
allocation that an op exposes (the section on address policies). It is not
an item of the module. A run of the spec may follow any policy, so the
spec's runs are those of every policy (the section on runs under every
address policy), while `fir-ref` follows the canonical layout, the policy
that proposes nothing. So a run made from its module gives the canonical
policy, and the spec's runs replace it by each policy in turn.

It carries the run's address resolver for each memory too, by its number:
which allocation the run proposes for an integer that an op turns back
into a pointer (the section on address resolvers). `fir-ref` follows the
canonical resolver, which proposes none, so a run made from its module
gives it, and the spec's runs replace it by each resolver that they keep
(the section on runs under every address policy).

The record also lists the allocations that a run starts with: one for each
global of the table, in the table's order, then one for each function of
the table, in the table's order (the section on the memories a run starts
with). Each lives in the memory of its number for the whole
run, with the global's alignment, its constness, and its initializer's
units followed by zeros up to its size (the human's ruling of 2026-11-20 on
#237, Q1). A function's lives in memory 0 for the whole run, constant,
aligned to 1, with no units (the human's ruling of 2026-11-19 on #235,
Q1). The record gives, for each global's symbol, its memory and its
allocation's id there, which `globalAddr` reads (#237), and for each
function's symbol its allocation's id in memory 0, which `funcAddr` reads
(#235). A run holds the globals of its own function's table only (Q3):
a nested module's globals are its kernels', as an op of a table names only
the items of that table.

Every obligation and guarantee over the semantics with memory holds for
every such record, with no hypothesis on it, so for every address policy.
So the items that later ops name, such as the address of a function (#235)
or of a global (#237), are new fields of this record, which the run fills
from its module, and the statements of those obligations and guarantees
stay as they are.

A run's record and validation read a table's layouts alike: each takes the
first layout with a symbol, so an op that validation accepts finds, in
every run, the layout it was checked against (`RunItems.ofTable_ref`).
They read its globals alike too: each takes the first global with a
symbol, so an op that validation accepts finds, in every run, a global of
the memory it was checked against (`RunItems.ofTable_globalMem`). And they
read its functions alike: the run gives an allocation to each symbol that
names a function of the table, as validation reads the table's symbols,
and to no other (`RunItems.ofTable_func`), and the allocations of two
symbols differ (`RunItems.ofTable_func_ne`).
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

/-- An allocation that a run starts with, in the memory that the module's
data layout numbers `mem`: its kind, its alignment, whether it is
constant, and its units in a memory whose units are `u` bits wide. A
global's is one (ADR-2026-11-09-1546), and a function's is another, of the
kind `function` (the human's ruling of 2026-11-19 on #235, Q1). -/
structure StartAlloc where
  mem : Nat
  kind : Memory.AllocKind
  align : Nat
  const : Bool
  units : (u : Nat) → List (Memory.MemUnit u)

/-- The items of a module that a run gives each op's rule: the layout of
each aggregate, by its symbol, if there is one, the address policy and
resolver of each memory, by its number, which are the canonical ones unless
the run says otherwise, the allocations the run starts with, in order, and
where each global starts, by its symbol, if there is one: its memory and
its allocation's id in that memory, and where each function starts, by its
symbol, if there is one: its allocation's id in memory 0. -/
structure RunItems where
  layout? : Name → Option LayoutPlace
  addrs : Nat → Memory.Policy := fun _ => Memory.Policy.canonical
  resolvers : Nat → Memory.Resolver := fun _ => Memory.Resolver.canonical
  starts : List StartAlloc := []
  global? : Name → Option (Nat × Memory.AllocId) := fun _ => none
  func? : Name → Option Memory.AllocId := fun _ => none

/-- The items of a run that gives no item, under the canonical layout. -/
def RunItems.empty : RunItems := { layout? := fun _ => none }

/-- The items `L` under the address policy `g` of each memory. -/
def RunItems.withAddrs (L : RunItems) (g : Nat → Memory.Policy) : RunItems := { L with addrs := g }

/-- The items `L` under the address resolver `k` of each memory. -/
def RunItems.withResolvers (L : RunItems) (k : Nat → Memory.Resolver) : RunItems :=
  { L with resolvers := k }

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

/-- Where a run starts the global `s` of a table whose globals are `gs`:
its memory, and its allocation's id in that memory, which counts the
globals of that memory before it. The first global with the symbol is the
one, as validation reads it. -/
def Global.startId? (gs : List Global) (s : Name) : Option (Nat × Memory.AllocId) :=
  let i := gs.findIdx (·.name == s)
  match gs[i]? with
  | some g => some (g.mem, ((gs.take i).filter (·.mem == g.mem)).length)
  | none => none

/-- The units that a piece of an initializer gives in the memory `n`, of
`u`-bit units, of a module whose data layout is `l`, as an item of a table
whose globals are `gs`: the units it gives, each cut to `u` bits; its
zeros; or the address of a global plus its offset, as a store of that
pointer writes it (`encodePtr`), in as many units as `InitPiece.unitCount`
counts. An address of a symbol that names no global gives none, so the
units stay those that validation counts. -/
def InitPiece.startUnits (l : DataLayout) (gs : List Global) (n u : Nat) :
    InitPiece → List (Memory.MemUnit u)
  | .units us => us.map fun x => .bits (BitVec.ofNat u x)
  | .zeros k => List.replicate k (.bits 0)
  | .addr s k =>
    match Global.startId? gs s with
    | some (m, a) =>
      Memory.encodePtr m ((l.entry n).bitsUnits (l.entry m).pointer) (l.entry n).order
        (.value ⟨some a, k⟩)
    | none => []

/-- The allocation that a run starts a global with, as an item of a table
whose globals are `gs`, in a module whose data layout is `l`: of the kind
`global`, in its memory, with its alignment and constness, and its
initializer's units followed by zeros up to its size (the human's ruling
of 2026-11-20 on #237, Q1). An initializer longer than the size, which
validation rejects, is cut to it. -/
def Global.start (l : DataLayout) (gs : List Global) (g : Global) : StartAlloc :=
  { mem := g.mem, kind := .global, align := g.align, const := g.const,
    units := fun u =>
      let us := g.init.flatMap (·.startUnits l gs g.mem u)
      us.take g.size ++ List.replicate (g.size - us.length) (.bits 0) }

/-- The allocation that a run starts a function with (the human's ruling of
2026-11-19 on #235, Q1): of the kind `function`, in memory 0, aligned to 1,
constant, and with no units, so that every load and store through its
address faults. -/
def funcStart : StartAlloc :=
  { mem := 0, kind := .function, align := 1, const := true, units := fun _ => [] }

/-- Where a run starts the function `s` of a table whose globals are `gs`
and whose functions are `fs`: its allocation's id in memory 0, which counts
the globals of memory 0, which the run starts first, and the functions
before it. The first function with the symbol is the one, as a call finds
its callee. -/
def Func.startId? (gs : List Global) (fs : List (Func d)) (s : Name) : Option Memory.AllocId :=
  let i := fs.findIdx (·.name == s)
  match fs[i]? with
  | some _ => some ((gs.filter (·.mem == 0)).length + i)
  | none => none

/-- The items that a run of a function of the symbol table `t`, in a module
whose data layout is `l`, gives each op: the first aggregate's layout of
`t` with each symbol, placed, under the canonical layout, the allocation of
each of `t`'s globals, in order, then of each of its functions, in order,
where each global of `t` starts, as an address in an initializer reads it
(`Global.startId?`), and where each function of `t` starts
(`Func.startId?`). The layouts are placed once, not at each lookup. -/
def RunItems.ofTable (l : DataLayout) (t : SymbolTable d) : RunItems :=
  let placed := t.aggregates.map fun a => (a.name, a.place l)
  { layout? := fun s => placed.lookup s,
    starts := t.globals.map (Global.start l t.globals) ++ t.funcs.map fun _ => funcStart,
    global? := Global.startId? t.globals, func? := Func.startId? t.globals t.funcs }

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

/-- The run gives an op the global that validation checks it against: the
first global of the table with each symbol starts in the memory that
validation sees for it (`SymbolTable.globalMems`). So an op that validation
accepts in a table finds its global, of the same memory, in each run of a
function of the table. -/
theorem RunItems.ofTable_globalMem (l : DataLayout) (t : SymbolTable d) (s : Name) :
    ((RunItems.ofTable l t).global? s).map (·.1) = t.globalMems s := by
  show (Global.startId? t.globals s).map (·.1) = (t.globals.find? (·.name == s)).map (·.mem)
  unfold Global.startId?
  rw [List.find?_eq_getElem?_findIdx]
  dsimp only
  split <;> rename_i h <;> simp [h]

/-- The run gives an allocation to each symbol that names a function of the
table, as validation reads the table's symbols (`SymbolTable.symbols`),
and to no other. So an op that validation accepts in a table, naming a
function, finds its allocation in each run of a function of the table. -/
theorem RunItems.ofTable_func (l : DataLayout) (t : SymbolTable d) (s : Name) :
    ((RunItems.ofTable l t).func? s).isSome = (t.symbols s).isSome := by
  show (Func.startId? t.globals t.funcs s).isSome = ((t.funcs.find? (·.name == s)).map _).isSome
  unfold Func.startId?
  rw [List.find?_eq_getElem?_findIdx]
  dsimp only
  split <;> rename_i h <;> simp [h]

/-- The run gives two symbols different allocations. -/
theorem RunItems.ofTable_func_ne (l : DataLayout) (t : SymbolTable d) {s s' : Name}
    {a a' : Memory.AllocId} (hs : (RunItems.ofTable l t).func? s = some a)
    (hs' : (RunItems.ofTable l t).func? s' = some a') (hne : s ≠ s') : a ≠ a' := by
  change Func.startId? t.globals t.funcs s = some a at hs
  change Func.startId? t.globals t.funcs s' = some a' at hs'
  unfold Func.startId? at hs hs'
  dsimp only at hs hs'
  split at hs
  case h_2 => cases hs
  rename_i f hf
  split at hs'
  case h_2 => cases hs'
  rename_i f' hf'
  cases hs
  cases hs'
  intro heq
  have hi : t.funcs.findIdx (·.name == s) = t.funcs.findIdx (·.name == s') := Nat.add_left_cancel heq
  have hn := List.findIdx_of_getElem?_eq_some hf
  have hn' := List.findIdx_of_getElem?_eq_some hf'
  rw [hi, hf'] at hf
  cases hf
  simp only [beq_iff_eq] at hn hn'
  exact hne (hn.symm.trans hn')

end Fir
