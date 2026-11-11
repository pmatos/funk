import Fir.Execution.MemoryState
import Fir.Execution.SetRuns

/-!
# How a run with memory ends

The proofs about runs read a run in the set monad path by path (the section
on how each step of a run ends). A run with memory is a run in the state
layer over the set monad, so a path of it also carries memories: it starts
from the memories as they are before it, and ends with them as they are
after it. This section reads such a run, _from_ given memories, as a
computation of the set monad whose results carry the memories they end
with. A path that ends stuck shows no memories, as a path that ends in UB
shows none: no outcome of a run looks at what a stuck path reached.

Read so, each piece from which the interpreter builds a run ends as the
section on how each step of a run ends says, with the memories threaded
through:

* `pure a` ends with `a`, and the memories it started from;
* a sequence, a computation and then a second one on its result, runs the
  second from the memories that the first ended with;
* the interpreter's own checks end where they end, and keep the memories;
* an op's rule ends as its semantics in the layer ends, from those
  memories;
* a call's frame runs its callee from the memories with a new frame
  entered, and leaves the frame on each path that ends with a result.

So every proof about runs in the set monad that follows a run step by step
has its counterpart for runs with memory: the same steps, each from the
memories that the step before it ended with.

A run of ops gives, beside its result, the steps of fuel it leaves. Read
from given memories, its result carries the memories it ends with beside
the values it returns, and a path out of fuel shows none.
-/

namespace Fir

open SetM Memory

variable {σ ε α β : Type}

/-- The computation `x` of the interpreter in the state layer, run from the
memories `S` and read in the set monad: each way it may end, a result with
the memories it ends with, an error, or UB. -/
def fromState (x : ExceptT ε (StateT σ SetM) α) (S : σ) : ExceptT ε SetM (α × σ) :=
  ExceptT.mk ((fun p : Except ε α × σ => (·, p.2) <$> p.1) <$> x.run S)

/-- `pure a`, from `S`, ends with `a` and `S`. -/
theorem fromState_pure (a : α) (S : σ) :
    fromState (pure a : ExceptT ε (StateT σ SetM) α) S = pure (a, S) := by
  show ExceptT.mk (_ <$> (pure (Except.ok a, S) : SetM _)) = _
  rw [map_pure]
  rfl

/-- `x >>= g`, from `S`, runs `x` from `S`, then `g` on its result from the
memories it ended with. -/
theorem fromState_bind (x : ExceptT ε (StateT σ SetM) α) (g : α → ExceptT ε (StateT σ SetM) β)
    (S : σ) : fromState (x >>= g) S = fromState x S >>= fun p => fromState (g p.1) p.2 := by
  have h : (x >>= g).run S = x.run S >>= fun p => ExceptT.bindCont g p.1 p.2 := rfl
  simp only [fromState, h]
  show ExceptT.mk _ = ExceptT.mk ((_ <$> x.run S) >>= ExceptT.bindCont _)
  rw [map_bind, bind_map_left]
  refine congrArg ExceptT.mk (congrArg (x.run S >>= ·) (funext fun p => ?_))
  obtain ⟨r, S'⟩ := p
  cases r with
  | ok a => rfl
  | error e =>
    show _ <$> (pure _ : SetM _) = _
    rw [map_pure]
    rfl

/-- A check of the interpreter, from `S`, ends where it ends, and keeps
`S`. -/
theorem fromState_liftExcept (x : Except ε α) (S : σ) :
    fromState (liftExcept x : ExceptT ε (StateT σ SetM) α) S = liftExcept ((·, S) <$> x) := by
  cases x with
  | ok a => exact fromState_pure a S
  | error e =>
    show ExceptT.mk (_ <$> (pure (Except.error e, S) : SetM _)) = _
    rw [map_pure]
    rfl

/-- A computation of the layer, lifted into the interpreter's, from `S`,
ends as it ends from `S`. -/
theorem fromState_lift (c : StateT σ SetM α) (S : σ) :
    fromState (ExceptT.lift c : ExceptT ε (StateT σ SetM) α) S = ExceptT.lift (c S) := by
  show ExceptT.mk (_ <$> ((fun p : α × σ => (Except.ok p.1, p.2)) <$> c S)) =
    ExceptT.mk (Except.ok <$> c S)
  rw [Functor.map_map]
  rfl

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

/-- A computation run as a call's frame, from `S`, runs from `S` with a new
frame entered, and leaves the frame on each path that ends with a result. -/
theorem fromState_inFrame (x : ExceptT ε (StateT (Memories Mem unit) SetM) α)
    (S : Memories Mem unit) :
    fromState (inFrame x) S = (fun p => (p.1, p.2.exit)) <$> fromState x S.enter := by
  have h : (inFrame x).run S = (fun r : Except ε α × Memories Mem unit => (r.1, r.2.exit)) <$>
    x.run S.enter := rfl
  apply ExceptT.ext
  simp only [ExceptT.run_map, fromState, ExceptT.run_mk, h, Functor.map_map]
  refine congrArg (· <$> x.run S.enter) (funext fun p => ?_)
  obtain ⟨r, S'⟩ := p
  cases r <;> rfl

/-! # Runs of ops -/

/-- A way a run of ops in the state layer ends, with the memories it ends
with beside the values it returns. A path out of fuel shows no memories. -/
def Result.withState : Result (α × Nat) × σ → Result ((α × σ) × Nat)
  | (.ret (a, k), S) => .ret ((a, S), k)
  | (.fuelExhausted, _) => .fuelExhausted

/-- A run of ops in the state layer, from the memories `S`, read in the set
monad: its returns carry the memories they end with. -/
def runFrom (x : ExceptT Stuck (StateT σ SetM) (Result (α × Nat))) (S : σ) :
    ExceptT Stuck SetM (Result ((α × σ) × Nat)) :=
  Result.withState <$> fromState x S

/-- A run of ops that starts with a computation runs the rest from the
memories that the computation ended with. -/
theorem runFrom_bind (x : ExceptT Stuck (StateT σ SetM) β)
    (g : β → ExceptT Stuck (StateT σ SetM) (Result (α × Nat))) (S : σ) :
    runFrom (x >>= g) S = fromState x S >>= fun p => runFrom (g p.1) p.2 := by
  simp only [runFrom, fromState_bind, map_bind]

/-- A return, from `S`, returns with `S`. -/
theorem runFrom_ret (a : α) (k : Nat) (S : σ) :
    runFrom (pure (.ret (a, k)) : ExceptT Stuck (StateT σ SetM) (Result (α × Nat))) S =
      pure (.ret ((a, S), k)) := by
  simp only [runFrom, fromState_pure, map_pure]
  rfl

/-- A run out of fuel is out of fuel from any memories. -/
theorem runFrom_exhausted (S : σ) :
    runFrom (pure .fuelExhausted : ExceptT Stuck (StateT σ SetM) (Result (α × Nat))) S =
      pure .fuelExhausted := by
  simp only [runFrom, fromState_pure, map_pure]
  rfl

/-- A stuck path is stuck from any memories. -/
theorem runFrom_stuck (r : String) (S : σ) :
    runFrom (liftExcept (stuck r) : ExceptT Stuck (StateT σ SetM) (Result (α × Nat))) S =
      liftExcept (stuck r) := by
  simp only [runFrom, fromState_liftExcept]
  apply ExceptT.ext
  simp only [ExceptT.run_map]
  show Except.map _ <$> (pure _ : SetM _) = _
  rw [map_pure]
  rfl

end Fir
