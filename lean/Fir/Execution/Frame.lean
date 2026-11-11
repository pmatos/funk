import Fir.Execution.Behaviour

/-!
# The frame effect

The interpreter runs every function in a frame of its own: it enters a
frame when the function starts and leaves it when the function returns.
What a frame does is the monad's, the _frame effect_ below, so the
interpreter knows nothing of memory (ADR-2026-10-29-2016). In a monad with
memory, leaving a call's frame frees the stack allocations that the call
made (ADR-2026-11-09-1548, the section on the memories of a run). An op
never asks for the frame effect: it is the interpreter's hook.

A monad with no memory has frames all the same: running a call in a frame
is then running the call. The set monad is such a monad, and so is the tree
of choices, so their runs are the runs of M0.
-/

namespace Fir

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
