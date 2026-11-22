import Fir.Core.Pointer
import Fir.Core.Signature
import Fir.Execution.RunItems

/-!
# Global address rules

This section gives `globalAddr` its rule (#237). Each global is one
allocation of kind `global`, live for the whole run (ADR-2026-11-09-1546):
a run starts with one allocation for each global of its function's table,
in the global's memory, and in each memory the globals of the table take
the ids from 0 up, in the table's order (the section on the memories a run
starts with). The run gives each op, for each global's symbol, its memory
and its allocation's id there (the section on the items a run gives each
op), the same id that an address of the global in an initializer holds
(`InitPiece.startUnits`). `globalAddr s n` gives a pointer of `ptr<N>`,
`N = n`, to the first unit of the global `s`: the pointer whose provenance
is that allocation, at offset 0.

In a table whose globals are `@msg`, then `@table`, both of memory 0, a
run starts `@msg` as memory 0's allocation 0 and `@table` as its
allocation 1, so `globalAddr "table" 0` gives the pointer of provenance 1
at offset 0. A load or a store through it, or through a pointer that
`ptradd` moves from it, reaches the global's units, and a store to a
constant global faults: it is UB when it runs (the human's ruling of
2026-11-20 on #237, Q2).

Validation requires that `s` name a global of the op's table in the memory
`N` (the section on the core rules of an op). The rule itself holds for
every record that a run may give: one that has no global `s` gives the
pointer with no provenance at offset 0, through which every access is
UB, so the op is never UB and never gives poison, for every record, with
no hypothesis on it.
-/

namespace Fir.Core

open Memory

/-- The rule of `globalAddr`, where the run gives where its global starts,
`g`: the pointer to the first unit of the global's allocation, and the
pointer with no provenance at offset 0 when the run gives no global. -/
def globalAddrValue : Option (Nat × AllocId) → Pointer
  | some (_, a) => ⟨some a, 0⟩
  | none => ⟨none, 0⟩

/-- The result of `globalAddr s n`, where the run gives where its global
starts, `g`: one pointer, never poison. -/
def globalAddrResult (g : Option (Nat × AllocId)) {n : Nat} : HVector toType [Ty.ptr n] :=
  .cons (.value (globalAddrValue g)) .nil

-- `@table`, memory 0's allocation 1: a pointer to its first unit. A
-- record with no such global gives the pointer with no provenance.
#guard globalAddrValue (some (0, 1)) == ⟨some 1, 0⟩ &&
  globalAddrValue (some (3, 0)) == ⟨some 0, 0⟩ &&
  globalAddrValue none == ⟨none, 0⟩

end Fir.Core
