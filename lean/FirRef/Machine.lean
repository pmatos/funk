import FirRef.BindingsSteps
import FirRef.RunAt

/-!
`fir-ref run` runs the spec's interpreter in the state layer over the tree of
choices, from the memories that hold the run's globals, and walks the tree
(`docs/decisions/fir-ref-command-line.md#scripted-and-exhaustive-modes`, the
spec's section on modes with memory). The spec's `Func.runOps` recurses once
per op it runs, through the tree's `bind`, and a call runs its callee inside
the caller's recursion, so the compiled interpreter takes stack for every step
and for every level of calls (#47). This module is the machine that `fir-ref`
runs instead (`docs/decisions/fir-ref-fast-paths.md#running`):
`Machine.advance` takes the steps of a run in a loop whose recursive calls are
all tail calls, and keeps each caller that waits for its callee on an explicit
stack of frames. It stops where the run ends or makes a choice, and gives what
is left after each value of the choice as a state of the machine, so that the
walkers of `FirRef.RunModes` can follow one path or every path without stack
per step.

Each step of the machine is one case of `Func.runOps`'s definition. It calls
the dialect's rules as the spec does, and keeps the values that the run has
defined in `FirRef.Bindings`, in place of the spec's list `Env`, so that the
lookups of a run take time near linear in the values it binds and the lookups
it makes, not in the values defined after each operand
(`docs/decisions/fir-ref-fast-paths.md#the-bindings-map`). `Bindings.args`,
`bindResults`, `bind`, `jump` and `enter` are `Env.operands`, `Env.bind`,
`Func.jump` and `Func.enter` on bindings, proved to fit them in
`FirRef.BindingsSteps`.

The machine carries the memories of the run
(`docs/decisions/fir-ref-memory.md#the-modes-run-with-memory`). A state that
runs ops holds the memories they start from, an op's tree holds the memories
after each of its paths, and a function that returns holds the memories it
returns with. Each function runs in a frame of its own: the machine enters a
frame where it starts a callee, and leaves it where the callee returns, as the
spec's frame does. The run's return is seen by a function `fin` of its values
and of the memories at its end, after its frame is left: as its values by
the modes that the core's and `gpu`'s `@[csimp]` theorems name, and at its end
by those of `fir-ref run --world` (`FirRef.Run`). Any other path that ends
drops its memories, and the machine does not leave the frames of the callers
that wait.

`Machine.advance_tree` (`FirRef.MachineTree`) proves that the machine
computes the spec's tree: a state stands for the spec's tree of what is
left of the run, `Cur.denote` for the function that runs and `kont` for the
callers that wait, each in the spec environment of its bindings
(`Bindings.toEnv`), and what `advance` gives stands for the same tree.
-/

namespace FirRef.Machine

open Fir Memory

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] {ε σ : Type}

/-- A caller that waits for its callee: the call `o` to `@s` of the
function `f`, in the environment `env`, with the ops `os` after it and `n`
steps left after the call's own step. -/
structure Frame (d : Dialect) [TyDenote d.Ty] where
  n : Nat
  f : Func d
  env : Bindings d
  o : Operation d
  os : List (Operation d)
  s : Name

/-- What the function that runs has left to do, with the run's state, of
type `σ`: the memories of the run. -/
inductive Cur (d : Dialect) [TyDenote d.Ty] [DialectSignature d] (ε σ : Type) where
  /-- Run the ops `os` of a block of `f`, with `n` steps, from the state
  `S`. -/
  | ops (n : Nat) (f : Func d) (env : Bindings d) (os : List (Operation d)) (S : σ)
  /-- The op `o`, which is not a terminator and calls no function, gives
  its results and the state after it by the tree `t`; then the ops `os`
  run. -/
  | den (n : Nat) (f : Func d) (env : Bindings d) (o : Operation d) (os : List (Operation d))
      (t : ChoiceTree ε (HVector toType (returnTypes o.op) × σ))
  /-- The terminator `o`, on the operands `args`, goes where the tree `t`
  says, with the state after it. -/
  | ex (n : Nat) (f : Func d) (env : Bindings d) (o : Operation d)
      (args : HVector toType (sig o.op)) (t : ChoiceTree ε (Exit × σ))
  /-- The function returns `vs` and leaves `k` steps, in the state `S`. -/
  | ret (vs : List (DVal d)) (k : Nat) (S : σ)

/-- How a path of a run ends, where a return is seen as a value of type `R`:
by default its values. -/
abbrev Leaf (d : Dialect) [TyDenote d.Ty] (ε : Type) (R : Type := List (DVal d)) :=
  ChoiceTree.Leaf ε (Except Stuck (Result R))

/-- Where the machine stops: at the end of a path, or at a choice of `w`
bits, with the state that the run goes on from for each value. -/
inductive Stop (d : Dialect) [TyDenote d.Ty] [DialectSignature d] (ε σ R : Type) where
  | leaf (l : Leaf d ε R)
  | choose (w : Nat) (c : ChoiceKind) (k : BitVec w → Cur d ε σ × List (Frame d))

/-- A measure of a state that each step of `advance` lowers. -/
def Cur.rank : Cur d ε σ → Nat
  | .ops n .. => 4 * n + 1
  | .den n .. | .ex n .. => 4 * n + 4
  | .ret _ k _ => 4 * k + 2

variable {N : Type} [DecidableEq N] {unit : N → Nat}
  [DecidableEq d.Ty] [DialectCall d] [DialectDenote d (StateT (Memories N unit) (ChoiceTree ε))]

local notation "SM" => StateT (Memories N unit) (ChoiceTree ε)

variable {R : Type}

set_option wf.preprocess false in
/-- The steps of a run from the state `c`, with the callers `st` waiting,
up to the end of the path or its next choice, where a return of the values
`vs` with the memories `S` at its end is seen as `fin vs S`. Its recursive
calls are tail calls. -/
def advance (M : Module d) (fin : List (DVal d) → Memories N unit → R) :
    Cur d ε (Memories N unit) → List (Frame d) → Stop d ε (Memories N unit) R
  | .ops 0 _ _ _ _, _ => .leaf (.ok (.ok .fuelExhausted))
  | .ops (_ + 1) _ _ [] _, _ => .leaf (.ok (stuck "a block ends without a terminator"))
  | .ops (n + 1) f env (o :: os) S, st =>
    if o.ownsCoreRegion then
      .leaf (.ok (stuck "an op owns a region of the core's kind, and no rule runs one"))
    else match env.args (sig o.op) o.operands with
    | .error e => .leaf (.ok (.error e))
    | .ok (args, env) =>
      if isTerminator o.op then
        if !os.isEmpty then .leaf (.ok (stuck "an op follows the terminator of its block"))
        else advance M fin (.ex n f env o args ((DialectDenote.exit (m := SM) o.op args).run S)) st
      else match callee? o.op with
        | none =>
          advance M fin (.den n f env o os ((DialectDenote.denote (m := SM) o.op args).run S)) st
        | some s => match M.func? s with
          | none =>
            if M.declares s (sig o.op) (returnTypes o.op) then .leaf (.ub extCallUB)
            else .leaf (.ok (stuck s!"@{s} is not a function or a declaration of the call's types"))
          | some g => match Bindings.enter g args with
            | .error e => .leaf (.ok (.error e))
            | .ok (body, genv) =>
              advance M fin (.ops n g genv body S.enter) (⟨n, f, env, o, os, s⟩ :: st)
  | .den n f env o os t, st => match t with
    | .pure (rs, S) =>
      match env.bindResults o.results rs
        "an op names a number of results other than it gives" with
      | .ok env' => advance M fin (.ops n f env' os S) st
      | .error e => .leaf (.ok (.error e))
    | .ub r => .leaf (.ub r)
    | .noOutcome e => .leaf (.noOutcome e)
    | .choose w c k => .choose w c fun b => (.den n f env o os (k b), st)
  | .ex n f env o args t, st => match t with
    | .pure (.ret, S) =>
      if sig o.op = f.results then advance M fin (.ret args.toDVals n S) st
      else .leaf (.ok (stuck "the function returns values of types other than its result types"))
    | .pure (.goto i, S) => match Bindings.jump f env o.succs i with
      | .ok (b, env') => advance M fin (.ops n f env' b.body S) st
      | .error e => .leaf (.ok (.error e))
    | .ub r => .leaf (.ub r)
    | .noOutcome e => .leaf (.noOutcome e)
    | .choose w c k => .choose w c fun b => (.ex n f env o args (k b), st)
  | .ret vs _ S, [] => .leaf (.ok (.ok (.ret (fin vs S.exit))))
  | .ret vs k S, fr :: st =>
    if vs.map (·.1) = returnTypes fr.o.op then
      match fr.env.bind fr.o.results vs
        "an op names a number of results other than it gives" with
      | .ok env' => advance M fin (.ops (min k fr.n) fr.f env' fr.os S.exit) st
      | .error e => .leaf (.ok (.error e))
    else .leaf (.ok (stuck s!"@{fr.s} returns values of types other than its call's result types"))
termination_by c => c.rank
decreasing_by
  all_goals simp only [Cur.rank]
  all_goals omega

/-! # What a state stands for -/

/-- The run's paths from a state, each with how it ends and the memories at
its end. -/
abbrev Paths (d : Dialect) [TyDenote d.Ty] (ε σ : Type) :=
  ChoiceTree ε (Except Stuck (Result (List (DVal d) × Nat)) × σ)

/-- The spec's tree of what is left of the run of the function that the
state `c` runs, in the spec's environment of its bindings. -/
def Cur.denote (M : Module d) : Cur d ε (Memories N unit) → Paths d ε (Memories N unit)
  | .ops n f env os S => runAt (Func.runOps M n f env.toEnv os) S
  | .den n f env o os t => t.bind fun p => runAt (afterDenote M n f env.toEnv o os p.1) p.2
  | .ex n f env o args t => t.bind fun p => runAt (afterExit M n f env.toEnv o args p.1) p.2
  | .ret vs k S => .pure (.ok (.ret (vs, k)), S)

/-- What the caller of a frame does after its callee's path ends with `p`,
as the spec computes it: it leaves the callee's frame, then goes on unless
the path is stuck. -/
def Frame.cont (M : Module d) (fr : Frame d) :
    Except Stuck (Result (List (DVal d) × Nat)) × Memories N unit →
      Paths d ε (Memories N unit) :=
  fun p => thenAt (afterCall M fr.n fr.f fr.env.toEnv fr.o fr.os fr.s) (p.1, p.2.exit)

/-- What `Func.run` does with what its function gives. -/
def finish {m : Type → Type} [Monad m] :
    Result (List (DVal d) × Nat) → ExceptT Stuck m (Result (List (DVal d)))
  | .ret (vs, _) => pure (.ret vs)
  | .fuelExhausted => pure .fuelExhausted

/-- The spec's tree of the rest of a run whose function that runs has the
paths `x`, with the callers `st` waiting, the innermost first. -/
def kont (M : Module d) : List (Frame d) → Paths d ε (Memories N unit) →
    ChoiceTree ε (Except Stuck (Result (List (DVal d))) × Memories N unit)
  | [], x => x.bind fun p => thenAt finish (p.1, p.2.exit)
  | fr :: st, x => kont M st (x.bind (fr.cont M))

/-- How a path ends, from how it ends with the memories at its end, where a
return of the values `vs` with the memories `S` is seen as `fin vs S`. -/
def endWith {σ : Type} (fin : List (DVal d) → σ → R) :
    Except Stuck (Result (List (DVal d))) × σ → Except Stuck (Result R)
  | (.ok (.ret vs), S) => .ok (.ret (fin vs S))
  | (.ok .fuelExhausted, _) => .ok .fuelExhausted
  | (.error e, _) => .error e

omit [DialectSignature d] [DecidableEq d.Ty] [DialectCall d] in
/-- Seeing a return as its values drops the memories. -/
theorem endWith_vals {σ : Type} :
    endWith (d := d) (σ := σ) (fun vs _ => vs) = Prod.fst := by
  funext p
  rcases p with ⟨_ | _ | _, _⟩ <;> rfl

/-- The tree of the rest of a run from a state, where a return of the
values `vs` with the memories `S` at its end is seen as `fin vs S`. -/
def tree (M : Module d) (fin : List (DVal d) → Memories N unit → R) (c : Cur d ε (Memories N unit))
    (st : List (Frame d)) : ChoiceTree ε (Except Stuck (Result R)) :=
  endWith fin <$> kont M st (c.denote M)

/-- The tree of a path that ends at a leaf. -/
def leafTree {α : Type} : ChoiceTree.Leaf ε α → ChoiceTree ε α
  | .ok a => .pure a
  | .ub r => .ub r
  | .noOutcome e => .noOutcome e

/-- The tree that the machine stands for where it stops. -/
def Stop.tree (M : Module d) (fin : List (DVal d) → Memories N unit → R) :
    Stop d ε (Memories N unit) R → ChoiceTree ε (Except Stuck (Result R))
  | .leaf l => leafTree l
  | .choose w c k => .choose w c fun b => Machine.tree M fin (k b).1 (k b).2

/-! # The callers' rest of a run that ends or chooses

`FirRef.MachineTree` builds `Machine.advance_tree` on these. -/

section Proofs

variable (M : Module d) (fin : List (DVal d) → Memories N unit → R)

theorem kont_error : ∀ (st : List (Frame d)) (e : Stuck) (S : Memories N unit),
    endWith fin <$> kont (ε := ε) M st (.pure (.error e, S)) = .pure (.error e)
  | [], _, _ => rfl
  | _ :: st, e, S => kont_error st e S.exit

theorem kont_fuel : ∀ (st : List (Frame d)) (S : Memories N unit),
    endWith fin <$> kont (ε := ε) M st (.pure (.ok .fuelExhausted, S)) = .pure (.ok .fuelExhausted)
  | [], _ => rfl
  | _ :: st, S => kont_fuel st S.exit

theorem kont_ub (r : String) : ∀ st : List (Frame d),
    kont (ε := ε) (N := N) (unit := unit) M st (.ub r) = .ub r
  | [] => rfl
  | _ :: st => kont_ub r st

theorem kont_noOutcome (e : ε) : ∀ st : List (Frame d),
    kont (N := N) (unit := unit) M st (.noOutcome e) = .noOutcome e
  | [] => rfl
  | _ :: st => kont_noOutcome e st

theorem kont_choose (w : Nat) (c : ChoiceKind) : ∀ (st : List (Frame d))
    (k : BitVec w → Paths d ε (Memories N unit)),
    kont M st (.choose w c k) = .choose w c fun b => kont M st (k b)
  | [], _ => rfl
  | _ :: st, _ => kont_choose w c st _

end Proofs

end FirRef.Machine
