import Fir.Core.Pointer
import Fir.Core.Signature
import Fir.Execution.RunItems

/-!
# Function address rules

This section gives `funcAddr` its rule (#235). A function's address is an
allocation of the kind `function` (the human's ruling of 2026-11-19 on
#235, Q1): a run starts with one allocation for each function of its
function's table, in memory 0, live for the whole run, with no units, and
in memory 0 the functions take the ids after the globals of that memory,
in the table's order (the section on the memories a run starts with). The
run gives each op, for each function's symbol, its allocation's id there
(the section on the items a run gives each op). `funcAddr s n` gives a
pointer of `ptr<N>`, `N = n`, to the function `s`: the pointer whose
provenance is that allocation, at offset 0.

In a table whose only global is `@msg`, of memory 0, and whose functions
are `@f`, then `@g`, a run starts `@msg` as memory 0's allocation 0, `@f`
as its allocation 1 and `@g` as its allocation 2, so `funcAddr "g" 0`
gives the pointer of provenance 2 at offset 0. The allocation has no units,
so a load or a store through the pointer, or through one that `ptradd`
moves from it, is out of bounds: it is UB when it runs. Exposing it gives
each function an address of its own (the section on addresses), so two
functions' addresses differ, and `ptr_from_int` may turn that address back
into the function's pointer: the run's resolver picks among the
allocations that hold it.

Validation requires that `s` name a function of the op's table and that
`N` be 0 (the section on the core rules of an op), and a run of a valid
module gives each op an allocation for it (`RunItems.ofTable_func`). The
rule itself holds for every record that a run may give: one that has no
function `s`, or an op of another memory, gives the pointer with no
provenance at offset 0, through which every access is UB, so a pointer of
`ptr<N>` never names an allocation of another memory, and the op is never
UB and never gives poison, for every record, with no hypothesis on it.
-/

namespace Fir.Core

open Memory

/-- The rule of `funcAddr` in the memory `n`, where the run gives where its
function starts in memory 0, `f`: the pointer to the function's
allocation, and the pointer with no provenance at offset 0 when the run
gives no function, or the op's memory is not 0. -/
def funcAddrValue (n : Nat) : Option AllocId → Pointer
  | some a => if n = 0 then ⟨some a, 0⟩ else ⟨none, 0⟩
  | none => ⟨none, 0⟩

/-- The result of `funcAddr s n`, where the run gives where its function
starts, `f`: one pointer, never poison. -/
def funcAddrResult (f : Option AllocId) {n : Nat} : HVector toType [Ty.ptr n] :=
  .cons (.value (funcAddrValue n f)) .nil

-- `@g`, memory 0's allocation 2: a pointer to it. A record with no such
-- function, or an op of memory 1, gives the pointer with no provenance.
#guard funcAddrValue 0 (some 2) == ⟨some 2, 0⟩ &&
  funcAddrValue 1 (some 2) == ⟨none, 0⟩ &&
  funcAddrValue 0 none == ⟨none, 0⟩

end Fir.Core
