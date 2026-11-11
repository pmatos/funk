import Fir.Execution.Behaviour
import Fir.Memory.Frames

/-!
# The memory effect

Memory is an effect of a run, beside choice and UB: an op that loads, stores
or allocates asks the run for it, as `freeze` asks for a choice of bits. Two
classes give it. A dialect whose ops touch memory states its semantics in a
monad that has them, and any way of running a program that provides them
can run those ops (ADR-2026-10-29-2030).

* The _memory effect_ gives the four operations of the memory model on the
  memories of a run, each named by its memory: allocating, freeing, loading
  and storing. An access that faults is immediate UB, for the reason of its
  fault (ADR-2026-11-09-1542).
* The _frame effect_ runs a computation as the run of one call. The
  interpreter runs every function in a frame of its own, so that the stack
  allocations of a call are freed when the call returns
  (ADR-2026-11-09-1548). An op never asks for it: it is the interpreter's
  hook.

A monad with no memory has frames all the same: running a call in a frame
is then running the call. The set monad is such a monad, and so is the tree
of choices, so their runs are the runs of M0. The state layer of the next
sections adds the memories of a run to such a monad, and gives frames that
enter and leave a call.
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

/-- The frame effect: `frame x` runs `x` as the run of one call, which
enters a frame before it and leaves the frame after it. -/
class MonadFrame (m : Type → Type) where
  frame : {α : Type} → m α → m α

/-- The set monad has no memory, so a frame is the computation itself. -/
instance : MonadFrame SetM := ⟨fun x => x⟩

/-- A computation of the interpreter, which may also end stuck, run as one
call's frame. -/
def inFrame {ε α : Type} {m : Type → Type} [MonadFrame m] (x : ExceptT ε m α) : ExceptT ε m α :=
  ExceptT.mk (MonadFrame.frame x.run)

/-- In the set monad, a frame is the computation itself. -/
@[simp] theorem inFrame_setM {ε α : Type} (x : ExceptT ε SetM α) : inFrame x = x := rfl

end Fir
