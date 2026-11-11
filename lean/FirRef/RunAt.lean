import FirRef.Steps

/-!
`FirRef.Machine` runs the spec's interpreter in the state layer over the
tree of choices (the spec's section on modes with memory). A computation of
the interpreter there, run from given memories, is a tree whose leaves hold
how the path ends and the memories at its end. `runAt` names that tree, and
the lemmas below say what `pure`, a failed check, `bind`, a lifted
computation and a call's frame give from given memories. A frame enters the
call before its computation and leaves it after, so the machine enters a
frame where it starts a callee and leaves it where the callee returns.
-/

namespace FirRef.Machine

open Fir Memory

variable {σ ε α β : Type}

/-- The tree of the computation `x` of the interpreter, in the state layer
over the tree of choices, run from the state `S`. -/
def runAt (x : ExceptT Stuck (StateT σ (ChoiceTree ε)) α) (S : σ) :
    ChoiceTree ε (Except Stuck α × σ) :=
  x.run.run S

/-- What `g` gives after a path that ends with `p`: it runs from the state
that the path ends with, unless the path is stuck. -/
def thenAt (g : α → ExceptT Stuck (StateT σ (ChoiceTree ε)) β) :
    Except Stuck α × σ → ChoiceTree ε (Except Stuck β × σ)
  | (.ok a, S) => runAt (g a) S
  | (.error e, S) => .pure (.error e, S)

theorem runAt_pure (a : α) (S : σ) :
    runAt (pure a : ExceptT Stuck (StateT σ (ChoiceTree ε)) α) S = .pure (.ok a, S) := rfl

theorem runAt_error (e : Stuck) (S : σ) :
    runAt (liftExcept (.error e) : ExceptT Stuck (StateT σ (ChoiceTree ε)) α) S =
      .pure (.error e, S) := rfl

theorem runAt_bind (x : ExceptT Stuck (StateT σ (ChoiceTree ε)) α)
    (g : α → ExceptT Stuck (StateT σ (ChoiceTree ε)) β) (S : σ) :
    runAt (x >>= g) S = (runAt x S).bind (thenAt g) := by
  show ChoiceTree.bind _ _ = ChoiceTree.bind _ _
  congr 1
  funext p
  rcases p with ⟨_ | _, _⟩ <;> rfl

theorem runAt_lift_bind (y : StateT σ (ChoiceTree ε) α)
    (g : α → ExceptT Stuck (StateT σ (ChoiceTree ε)) β) (S : σ) :
    runAt (ExceptT.lift y >>= g) S = (y.run S).bind fun p => runAt (g p.1) p.2 := by
  rw [runAt_bind]
  show ((y.run S).bind fun p => .pure (Except.ok p.1, p.2)).bind (thenAt g) = _
  rw [ChoiceTree.bind_assoc]
  rfl

variable {N : Type} [DecidableEq N] {unit : N → Nat}

theorem runAt_inFrame (x : ExceptT Stuck (StateT (Memories N unit) (ChoiceTree ε)) α)
    (S : Memories N unit) :
    runAt (inFrame x) S = (runAt x S.enter).bind fun p => .pure (p.1, p.2.exit) := rfl

end FirRef.Machine
