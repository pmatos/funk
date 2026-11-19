import Fir.Validation.Layout
import Fir.Memory.Policy

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

Every obligation and guarantee over the semantics with memory holds for
every such record, with no hypothesis on it, so for every address policy.
So the items that later ops name, such as the address of a function (#235)
or of a global (#237), are new fields of this record, which the run fills
from its module, and the statements of those obligations and guarantees
stay as they are.
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
each aggregate, by its symbol, if there is one, and the address policy of
each memory, by its number, which is the canonical one unless the run says
otherwise. -/
structure RunItems where
  layout? : Name → Option LayoutPlace
  addrs : Nat → Memory.Policy := fun _ => Memory.Policy.canonical

/-- The items of a run that gives no item, under the canonical layout. -/
def RunItems.empty : RunItems := { layout? := fun _ => none }

/-- The items `L` under the address policy `g` of each memory. -/
def RunItems.withAddrs (L : RunItems) (g : Nat → Memory.Policy) : RunItems := { L with addrs := g }

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
`t` with each symbol, placed, under the canonical layout. The layouts are
placed once, not at each lookup. -/
def RunItems.ofTable (l : DataLayout) (t : SymbolTable d) : RunItems :=
  let placed := t.aggregates.map fun a => (a.name, a.place l)
  { layout? := fun s => placed.lookup s }

/-- The items that a run of a function of a module's own table gives each
op. -/
def Module.runItems (M : Module d) : RunItems := RunItems.ofTable M.layout M.table

end Fir
