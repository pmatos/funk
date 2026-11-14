import Fir.Execution.Frame
import Fir.Memory.Frames

/-!
# The memory effect

Memory is an effect of a run, beside choice and UB: an op that loads, stores
or allocates asks the run for it, as `freeze` asks for a choice of bits. A
dialect whose ops touch memory states its semantics in a monad that has the
memory effect, and any way of running a program that provides it can run
those ops (ADR-2026-10-29-2009).

The memory effect gives the four operations of the memory model on the
memories of a run, each named by its memory: allocating, freeing, loading
and storing. A load or a store is an aligned access: it carries the
alignment that the op promises, in units. An access that faults is
immediate UB, for the reason of its fault, a misaligned access included
(ADR-2026-11-09-1542; the human's ruling of 2026-11-11 on #231). The frames of calls are the frame effect's
(the section on the frame effect), which an op never asks for. The state
layer of the next section adds the memories of a run to a monad with no
memory, and gives both effects.
-/

namespace Fir

open Memory

/-- The memory effect, on memories named by `Mem` whose units are `unit x`
bits wide for the memory `x`: the four operations of the memory model. A
load or a store is aligned to a number of units, and one that faults,
misaligned or not, is immediate UB. -/
class MonadMemory (Mem : outParam Type) (unit : outParam (Mem → Nat)) (m : Type → Type) where
  /-- Allocates `n` units of the kind `k`, aligned to `al` units, in the
  memory `x`, and gives the pointer to the first one. -/
  alloc : (x : Mem) → (k : AllocKind) → (n al : Nat) → m Pointer
  /-- Frees the allocation `a` of the memory `x`. -/
  free : (x : Mem) → (a : AllocId) → m Unit
  /-- Loads `n` units of the memory `x` through `p`, an access aligned to
  `al` units. -/
  load : (x : Mem) → (p : Pointer) → (n al : Nat) → m (List (MemUnit (unit x)))
  /-- Stores the units `us` to the memory `x` through `p`, an access aligned
  to `al` units. -/
  store : (x : Mem) → (p : Pointer) → (us : List (MemUnit (unit x))) → (al : Nat) → m Unit

end Fir
