import Fir.Execution.Frame
import Fir.Memory.Frames

/-!
# The memory effect

Memory is an effect of a run, beside choice and UB: an op that loads, stores
or allocates asks the run for it, as `freeze` asks for a choice of bits. A
dialect whose ops touch memory states its semantics in a monad that has the
memory effect, and any way of running a program that provides it can run
those ops (ADR-2026-10-29-2030).

The memory effect gives the four operations of the memory model on the
memories of a run, each named by its memory: allocating, freeing, loading
and storing. An access that faults is immediate UB, for the reason of its
fault (ADR-2026-11-09-1542). The frames of calls are the frame effect's
(the section on the frame effect), which an op never asks for. The state
layer of the next section adds the memories of a run to a monad with no
memory, and gives both effects.
-/

namespace Fir

open Memory

/-- The memory effect, on memories named by `Mem` whose units are `unit x`
bits wide for the memory `x`: the four operations of the memory model. A
load or a store that faults is immediate UB. -/
class MonadMemory (Mem : outParam Type) (unit : outParam (Mem → Nat)) (m : Type → Type) where
  /-- Allocates `n` units of the kind `k` in the memory `x`, and gives the
  pointer to the first one. -/
  alloc : (x : Mem) → (k : AllocKind) → (n : Nat) → m Pointer
  /-- Frees the allocation `a` of the memory `x`. -/
  free : (x : Mem) → (a : AllocId) → m Unit
  /-- Loads `n` units of the memory `x` through `p`. -/
  load : (x : Mem) → (p : Pointer) → (n : Nat) → m (List (MemUnit (unit x)))
  /-- Stores the units `us` to the memory `x` through `p`. -/
  store : (x : Mem) → (p : Pointer) → (us : List (MemUnit (unit x))) → m Unit

end Fir
