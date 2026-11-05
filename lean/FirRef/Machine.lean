import FirRef.BindingsSteps
import FirRef.Steps

/-!
`fir-ref run` runs the spec's interpreter in the tree of choices and walks
the tree (ADR-2026-10-30-2218). The spec's `Func.runOps` recurses once per
op it runs, through the tree's `bind`, and a call runs its callee inside
the caller's recursion, so the compiled interpreter takes stack for every
step and for every level of calls (#47). This module is the machine that
`fir-ref` runs instead (ADR-2026-11-04-2132): `Machine.advance` takes the
steps of a run in a loop whose recursive calls are all tail calls, and
keeps each caller that waits for its callee on an explicit stack of
frames. It stops where the run ends or makes a choice, and gives what is
left after each value of the choice as a state of the machine, so that the
walkers of `FirRef.RunModes` can follow one path or every path without
stack per step.

Each step of the machine is one case of `Func.runOps`'s definition. It
calls the dialect's rules as the spec does, and keeps the values that the
run has defined in `FirRef.Bindings`, in place of the spec's list `Env`, so
that looking a name up does not take time for each value defined after it
(ADR-2026-11-05-0442). `Bindings.args`, `bindResults`, `bind`, `jump` and
`enter` are `Env.operands`, `Env.bind`, `Func.jump` and `Func.enter` on
bindings, proved to fit them in `FirRef.BindingsSteps`.

`Machine.advance_tree` (`FirRef.MachineTree`) proves that the machine
computes the spec's tree: a state stands for the spec's computation of
what is left of the run, `Cur.denote` for the function that runs and
`kont` for the callers that wait, each in the spec environment of its
bindings (`Bindings.toEnv`), and what `advance` gives stands for the same
tree.
-/

namespace FirRef.Machine

open Fir

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] {ε : Type}

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

/-- What the function that runs has left to do. -/
inductive Cur (d : Dialect) [TyDenote d.Ty] [DialectSignature d] (ε : Type) where
  /-- Run the ops `os` of a block of `f`, with `n` steps. -/
  | ops (n : Nat) (f : Func d) (env : Bindings d) (os : List (Operation d))
  /-- The op `o`, which is not a terminator and calls no function, gives
  its results by the tree `t`; then the ops `os` run. -/
  | den (n : Nat) (f : Func d) (env : Bindings d) (o : Operation d) (os : List (Operation d))
      (t : ChoiceTree ε (HVector toType (returnTypes o.op)))
  /-- The terminator `o`, on the operands `args`, goes where the tree `t`
  says. -/
  | ex (n : Nat) (f : Func d) (env : Bindings d) (o : Operation d)
      (args : HVector toType (sig o.op)) (t : ChoiceTree ε Exit)
  /-- The function returns `vs` and leaves `k` steps. -/
  | ret (vs : List (DVal d)) (k : Nat)

/-- How a path of a run ends. -/
abbrev Leaf (d : Dialect) [TyDenote d.Ty] (ε : Type) :=
  ChoiceTree.Leaf ε (Except Stuck (Result (List (DVal d))))

/-- Where the machine stops: at the end of a path, or at a choice of `w`
bits, with the state that the run goes on from for each value. -/
inductive Stop (d : Dialect) [TyDenote d.Ty] [DialectSignature d] (ε : Type) where
  | leaf (l : Leaf d ε)
  | choose (w : Nat) (k : BitVec w → Cur d ε × List (Frame d))

/-- A measure of a state that each step of `advance` lowers. -/
def Cur.rank : Cur d ε → Nat
  | .ops n .. => 4 * n + 1
  | .den n .. | .ex n .. => 4 * n + 4
  | .ret _ k => 4 * k + 2

variable [DecidableEq d.Ty] [DialectCall d] [DialectDenote d (ChoiceTree ε)]

set_option wf.preprocess false in
/-- The steps of a run from the state `c`, with the callers `st` waiting,
up to the end of the path or its next choice. Its recursive calls are tail
calls. -/
def advance (M : Module d) : Cur d ε → List (Frame d) → Stop d ε
  | .ops 0 _ _ _, _ => .leaf (.ok (.ok .fuelExhausted))
  | .ops (_ + 1) _ _ [], _ => .leaf (.ok (stuck "a block ends without a terminator"))
  | .ops (n + 1) f env (o :: os), st =>
    if !o.regions.isEmpty then .leaf (.ok (stuck "an op owns a region, and no rule runs one"))
    else match env.args (sig o.op) o.operands with
    | .error e => .leaf (.ok (.error e))
    | .ok (args, env) =>
      if isTerminator o.op then
        if !os.isEmpty then .leaf (.ok (stuck "an op follows the terminator of its block"))
        else advance M (.ex n f env o args (DialectDenote.exit o.op args)) st
      else match callee? o.op with
        | none => advance M (.den n f env o os (DialectDenote.denote o.op args)) st
        | some s => match M.func? s with
          | none => .leaf (.ok (stuck s!"@{s} is not a function of the module"))
          | some g => match Bindings.enter g args with
            | .error e => .leaf (.ok (.error e))
            | .ok (body, genv) => advance M (.ops n g genv body) (⟨n, f, env, o, os, s⟩ :: st)
  | .den n f env o os t, st => match t with
    | .pure rs =>
      match env.bindResults o.results rs
        "an op names a number of results other than it gives" with
      | .ok env' => advance M (.ops n f env' os) st
      | .error e => .leaf (.ok (.error e))
    | .ub r => .leaf (.ub r)
    | .noOutcome e => .leaf (.noOutcome e)
    | .choose w k => .choose w fun b => (.den n f env o os (k b), st)
  | .ex n f env o args t, st => match t with
    | .pure .ret =>
      if sig o.op = f.results then advance M (.ret args.toDVals n) st
      else .leaf (.ok (stuck "the function returns values of types other than its result types"))
    | .pure (.goto i) => match Bindings.jump f env o.succs i with
      | .ok (b, env') => advance M (.ops n f env' b.body) st
      | .error e => .leaf (.ok (.error e))
    | .ub r => .leaf (.ub r)
    | .noOutcome e => .leaf (.noOutcome e)
    | .choose w k => .choose w fun b => (.ex n f env o args (k b), st)
  | .ret vs _, [] => .leaf (.ok (.ok (.ret vs)))
  | .ret vs k, fr :: st =>
    if vs.map (·.1) = returnTypes fr.o.op then
      match fr.env.bind fr.o.results vs
        "an op names a number of results other than it gives" with
      | .ok env' => advance M (.ops (min k fr.n) fr.f env' fr.os) st
      | .error e => .leaf (.ok (.error e))
    else .leaf (.ok (stuck s!"@{fr.s} returns values of types other than its call's result types"))
termination_by c => c.rank
decreasing_by
  all_goals simp only [Cur.rank]
  all_goals omega

/-! # What a state stands for -/

/-- The spec's computation of what is left of the run of the function that
the state `c` runs, in the spec's environment of its bindings. -/
def Cur.denote (M : Module d) : Cur d ε →
    ExceptT Stuck (ChoiceTree ε) (Result (List (DVal d) × Nat))
  | .ops n f env os => Func.runOps M n f env.toEnv os
  | .den n f env o os t => ExceptT.lift t >>= afterDenote M n f env.toEnv o os
  | .ex n f env o args t => ExceptT.lift t >>= afterExit M n f env.toEnv o args
  | .ret vs k => pure (.ret (vs, k))

/-- What the caller of a frame does with what its callee gives, as the spec
computes it. -/
def Frame.cont (M : Module d) (fr : Frame d) : Result (List (DVal d) × Nat) →
    ExceptT Stuck (ChoiceTree ε) (Result (List (DVal d) × Nat)) :=
  afterCall M fr.n fr.f fr.env.toEnv fr.o fr.os fr.s

/-- What `Func.run` does with what its function gives. -/
def finish : Result (List (DVal d) × Nat) → ExceptT Stuck (ChoiceTree ε) (Result (List (DVal d)))
  | .ret (vs, _) => pure (.ret vs)
  | .fuelExhausted => pure .fuelExhausted

/-- The spec's computation of the rest of a run whose function that runs
gives `x`, with the callers `st` waiting, the innermost first. -/
def kont (M : Module d) : List (Frame d) →
    ExceptT Stuck (ChoiceTree ε) (Result (List (DVal d) × Nat)) →
    ExceptT Stuck (ChoiceTree ε) (Result (List (DVal d)))
  | [], x => x >>= finish
  | fr :: st, x => kont M st (x >>= fr.cont M)

/-- The tree of the rest of a run from a state. -/
def tree (M : Module d) (c : Cur d ε) (st : List (Frame d)) :
    ChoiceTree ε (Except Stuck (Result (List (DVal d)))) :=
  (kont M st (c.denote M)).run

/-- The tree of a path that ends at a leaf. -/
def leafTree {α : Type} : ChoiceTree.Leaf ε α → ChoiceTree ε α
  | .ok a => .pure a
  | .ub r => .ub r
  | .noOutcome e => .noOutcome e

/-- The tree that the machine stands for where it stops. -/
def Stop.tree (M : Module d) : Stop d ε → ChoiceTree ε (Except Stuck (Result (List (DVal d))))
  | .leaf l => leafTree l
  | .choose w k => .choose w fun b => Machine.tree M (k b).1 (k b).2

/-! # The callers' rest of a run that ends or chooses

`FirRef.MachineTree` builds `Machine.advance_tree` on these. -/

section Proofs

variable (M : Module d)

theorem kont_error : ∀ (st : List (Frame d)) (e : Stuck),
    (kont (ε := ε) M st (liftExcept (.error e))).run = .pure (.error e)
  | [], _ => rfl
  | _ :: st, e => kont_error st e

theorem kont_fuel : ∀ st : List (Frame d),
    (kont (ε := ε) M st (pure .fuelExhausted)).run = .pure (.ok .fuelExhausted)
  | [] => rfl
  | _ :: st => kont_fuel st

theorem kont_ub (r : String) : ∀ st : List (Frame d),
    (kont (ε := ε) M st (ExceptT.mk (.ub r))).run = .ub r
  | [] => rfl
  | _ :: st => kont_ub r st

theorem kont_noOutcome (e : ε) : ∀ st : List (Frame d),
    (kont M st (ExceptT.mk (.noOutcome e))).run = .noOutcome e
  | [] => rfl
  | _ :: st => kont_noOutcome e st

theorem kont_choose (w : Nat) : ∀ (st : List (Frame d))
    (k : BitVec w → ChoiceTree ε (Except Stuck (Result (List (DVal d) × Nat)))),
    (kont M st (ExceptT.mk (.choose w k))).run =
      .choose w fun b => (kont M st (ExceptT.mk (k b))).run
  | [], _ => rfl
  | _ :: st, _ => kont_choose w st _

end Proofs

end FirRef.Machine
