import Fir.Execution.Modes

/-!
`fir-ref run` runs the spec's interpreter in the tree of choices and walks
the tree (ADR-2026-10-30-2218). The spec's `Func.runOps` recurses once per
op it runs, through the tree's `bind`, and a call runs its callee inside
the caller's recursion, so the compiled interpreter takes stack for every
step and for every level of calls (#47, ADR-2026-11-04-2132). This module is the machine that
`fir-ref` runs instead: `Machine.advance` takes the steps of a run in a
loop whose recursive calls are all tail calls, and keeps each caller that
waits for its callee on an explicit stack of frames. It stops where the run
ends or makes a choice, and gives what is left after each value of the
choice as a state of the machine, so that the walkers of `FirRef.RunModes`
can follow one path or every path without stack per step.

The theorem `Machine.advance_tree` proves that the machine computes the
spec's tree: a state stands for the spec's computation of what is left of
the run, `Cur.denote` for the function that runs and `kont` for the
callers that wait, and what `advance` gives stands for the same tree. No
step of the machine copies a spec function; each is one case of
`Func.runOps`'s definition, and the proof unfolds that definition once per
case.
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
  env : Env d
  o : Operation d
  os : List (Operation d)
  s : Name

/-- What the function that runs has left to do. -/
inductive Cur (d : Dialect) [TyDenote d.Ty] [DialectSignature d] (ε : Type) where
  /-- Run the ops `os` of a block of `f`, with `n` steps. -/
  | ops (n : Nat) (f : Func d) (env : Env d) (os : List (Operation d))
  /-- The op `o`, which is not a terminator and calls no function, gives
  its results by the tree `t`; then the ops `os` run. -/
  | den (n : Nat) (f : Func d) (env : Env d) (o : Operation d) (os : List (Operation d))
      (t : ChoiceTree ε (HVector toType (returnTypes o.op)))
  /-- The terminator `o`, on the operands `args`, goes where the tree `t`
  says. -/
  | ex (n : Nat) (f : Func d) (env : Env d) (o : Operation d) (args : HVector toType (sig o.op))
      (t : ChoiceTree ε Exit)
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
    else match env.operands (sig o.op) o.operands with
    | .error e => .leaf (.ok (.error e))
    | .ok args =>
      if isTerminator o.op then
        if !os.isEmpty then .leaf (.ok (stuck "an op follows the terminator of its block"))
        else advance M (.ex n f env o args (DialectDenote.exit o.op args)) st
      else match callee? o.op with
        | none => advance M (.den n f env o os (DialectDenote.denote o.op args)) st
        | some s => match M.func? s with
          | none => .leaf (.ok (stuck s!"@{s} is not a function of the module"))
          | some g => match g.enter args.toDVals with
            | .error e => .leaf (.ok (.error e))
            | .ok (body, genv) => advance M (.ops n g genv body) (⟨n, f, env, o, os, s⟩ :: st)
  | .den n f env o os t, st => match t with
    | .pure rs =>
      match env.bind (o.results.map (·.1)) rs.toDVals
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
    | .pure (.goto i) => match f.jump env o.succs i with
      | .ok (b, env') => advance M (.ops n f env' b.body) st
      | .error e => .leaf (.ok (.error e))
    | .ub r => .leaf (.ub r)
    | .noOutcome e => .leaf (.noOutcome e)
    | .choose w k => .choose w fun b => (.ex n f env o args (k b), st)
  | .ret vs _, [] => .leaf (.ok (.ok (.ret vs)))
  | .ret vs k, fr :: st =>
    if vs.map (·.1) = returnTypes fr.o.op then
      match fr.env.bind (fr.o.results.map (·.1)) vs
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
the state `c` runs. -/
def Cur.denote (M : Module d) : Cur d ε →
    ExceptT Stuck (ChoiceTree ε) (Result (List (DVal d) × Nat))
  | .ops n f env os => Func.runOps M n f env os
  | .den n f env o os t => ExceptT.lift t >>= fun rs => do
    let env' ← liftExcept (env.bind (o.results.map (·.1)) rs.toDVals
      "an op names a number of results other than it gives")
    Func.runOps M n f env' os
  | .ex n f env o args t => ExceptT.lift t >>= fun x => match x with
    | .ret =>
      if sig o.op = f.results then pure (.ret (args.toDVals, n))
      else liftExcept (stuck "the function returns values of types other than its result types")
    | .goto i => do
      let (b, env') ← liftExcept (f.jump env o.succs i)
      Func.runOps M n f env' b.body
  | .ret vs k => pure (.ret (vs, k))

/-- What the caller of a frame does with what its callee gives, as the spec
computes it. -/
def Frame.cont (M : Module d) (fr : Frame d) : Result (List (DVal d) × Nat) →
    ExceptT Stuck (ChoiceTree ε) (Result (List (DVal d) × Nat))
  | .fuelExhausted => pure .fuelExhausted
  | .ret (vs, k) =>
    if vs.map (·.1) = returnTypes fr.o.op then do
      let env' ← liftExcept (fr.env.bind (fr.o.results.map (·.1)) vs
        "an op names a number of results other than it gives")
      Func.runOps M (min k fr.n) fr.f env' fr.os
    else liftExcept (stuck s!"@{fr.s} returns values of types other than its call's result types")

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

/-! # The machine computes the spec's tree -/

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

theorem liftExcept_ok_bind {α β : Type} (a : α) (g : α → ExceptT Stuck (ChoiceTree ε) β) :
    (liftExcept (ε := Stuck) (.ok a) >>= g) = g a := rfl

variable {M} {n : Nat} {f : Func d} {env : Env d} {o : Operation d} {os : List (Operation d)}

theorem runOps_zero : Func.runOps (m := ChoiceTree ε) M 0 f env os = pure .fuelExhausted := by
  simp [Func.runOps]

theorem runOps_nil : Func.runOps (m := ChoiceTree ε) M (n + 1) f env [] =
    liftExcept (stuck "a block ends without a terminator") := by
  simp [Func.runOps]

theorem runOps_region (h : (!o.regions.isEmpty) = true) :
    Func.runOps (m := ChoiceTree ε) M (n + 1) f env (o :: os) =
      liftExcept (stuck "an op owns a region, and no rule runs one") := by
  rw [Func.runOps]
  simp only [h, ite_true]
  rfl

variable {args : HVector toType (sig o.op)}

theorem runOps_operands (h : (!o.regions.isEmpty) = false) {e : Stuck}
    (ha : env.operands (sig o.op) o.operands = .error e) :
    Func.runOps (m := ChoiceTree ε) M (n + 1) f env (o :: os) = liftExcept (.error e) := by
  rw [Func.runOps]
  simp only [h, ha]
  rfl

theorem runOps_follows (h : (!o.regions.isEmpty) = false)
    (ha : env.operands (sig o.op) o.operands = .ok args) (hT : isTerminator o.op = true)
    (hos : (!os.isEmpty) = true) :
    Func.runOps (m := ChoiceTree ε) M (n + 1) f env (o :: os) =
      liftExcept (stuck "an op follows the terminator of its block") := by
  rw [Func.runOps]
  simp only [h, ha, hT, hos]
  rfl

theorem runOps_exit (h : (!o.regions.isEmpty) = false)
    (ha : env.operands (sig o.op) o.operands = .ok args) (hT : isTerminator o.op = true)
    (hos : (!os.isEmpty) = false) :
    Func.runOps (m := ChoiceTree ε) M (n + 1) f env (o :: os) =
      (Cur.ex n f env o args (DialectDenote.exit o.op args)).denote M := by
  rw [Func.runOps]
  simp only [h, ha, hT, hos]
  rfl

theorem runOps_denote (h : (!o.regions.isEmpty) = false)
    (ha : env.operands (sig o.op) o.operands = .ok args) (hT : isTerminator o.op = false)
    (hc : callee? o.op = none) :
    Func.runOps (m := ChoiceTree ε) M (n + 1) f env (o :: os) =
      (Cur.den n f env o os (DialectDenote.denote o.op args)).denote M := by
  rw [Func.runOps]
  simp only [h, ha, hT, hc]
  rfl

theorem runOps_noFunc (h : (!o.regions.isEmpty) = false)
    (ha : env.operands (sig o.op) o.operands = .ok args) (hT : isTerminator o.op = false)
    {s : Name} (hc : callee? o.op = some s) (hg : M.func? s = none) :
    Func.runOps (m := ChoiceTree ε) M (n + 1) f env (o :: os) =
      liftExcept (stuck s!"@{s} is not a function of the module") := by
  rw [Func.runOps]
  simp only [h, ha, hT, hc, hg]
  rfl

theorem runOps_enter (h : (!o.regions.isEmpty) = false)
    (ha : env.operands (sig o.op) o.operands = .ok args) (hT : isTerminator o.op = false)
    {s : Name} (hc : callee? o.op = some s) {g : Func d} (hg : M.func? s = some g) {e : Stuck}
    (he : g.enter args.toDVals = .error e) :
    Func.runOps (m := ChoiceTree ε) M (n + 1) f env (o :: os) = liftExcept (.error e) := by
  rw [Func.runOps]
  simp only [h, ha, hT, hc, hg, Bool.false_eq_true, ↓reduceIte, liftExcept_ok_bind, he]
  rfl

theorem runOps_call (h : (!o.regions.isEmpty) = false)
    (ha : env.operands (sig o.op) o.operands = .ok args) (hT : isTerminator o.op = false)
    {s : Name} (hc : callee? o.op = some s) {g : Func d} (hg : M.func? s = some g)
    {body : List (Operation d)} {genv : Env d} (he : g.enter args.toDVals = .ok (body, genv)) :
    Func.runOps (m := ChoiceTree ε) M (n + 1) f env (o :: os) =
      Func.runOps M n g genv body >>= Frame.cont M ⟨n, f, env, o, os, s⟩ := by
  rw [Func.runOps]
  simp only [h, ha, hT, hc, hg, Bool.false_eq_true, ↓reduceIte, liftExcept_ok_bind, he]
  rfl

/-- What the machine gives where it stops stands for the spec's tree of the
rest of the run. -/
theorem advance_tree (c : Cur d ε) (st : List (Frame d)) :
    (advance M c st).tree M = tree M c st := by
  fun_induction advance M c st with
  | case1 f env os st =>
    show _ = (kont M st (Func.runOps M 0 f env os)).run
    rw [runOps_zero]; exact (kont_fuel M st).symm
  | case2 n f env st =>
    show _ = (kont M st (Func.runOps M (n + 1) f env [])).run
    rw [runOps_nil]; exact (kont_error M st _).symm
  | case3 n f env o os st h =>
    show _ = (kont M st (Func.runOps M (n + 1) f env (o :: os))).run
    rw [runOps_region h]; exact (kont_error M st _).symm
  | case4 n f env o os st h e ha =>
    show _ = (kont M st (Func.runOps M (n + 1) f env (o :: os))).run
    rw [runOps_operands (Bool.of_not_eq_true h) ha]; exact (kont_error M st _).symm
  | case5 n f env o os st h args ha hT hos =>
    show _ = (kont M st (Func.runOps M (n + 1) f env (o :: os))).run
    rw [runOps_follows (Bool.of_not_eq_true h) ha hT hos]; exact (kont_error M st _).symm
  | case6 n f env o os st h args ha hT hos ih =>
    rw [ih]
    show _ = (kont M st (Func.runOps M (n + 1) f env (o :: os))).run
    rw [runOps_exit (Bool.of_not_eq_true h) ha hT (Bool.of_not_eq_true hos)]; rfl
  | case7 n f env o os st h args ha hT hc ih =>
    rw [ih]
    show _ = (kont M st (Func.runOps M (n + 1) f env (o :: os))).run
    rw [runOps_denote (Bool.of_not_eq_true h) ha (Bool.of_not_eq_true hT) hc]; rfl
  | case8 n f env o os st h args ha hT s hc hg =>
    show _ = (kont M st (Func.runOps M (n + 1) f env (o :: os))).run
    rw [runOps_noFunc (Bool.of_not_eq_true h) ha (Bool.of_not_eq_true hT) hc hg]
    exact (kont_error M st _).symm
  | case9 n f env o os st h args ha hT s hc g hg e he =>
    show _ = (kont M st (Func.runOps M (n + 1) f env (o :: os))).run
    rw [runOps_enter (Bool.of_not_eq_true h) ha (Bool.of_not_eq_true hT) hc hg he]
    exact (kont_error M st _).symm
  | case10 n f env o os st h args ha hT s hc g hg body genv he ih =>
    rw [ih]
    show _ = (kont M st (Func.runOps M (n + 1) f env (o :: os))).run
    rw [runOps_call (Bool.of_not_eq_true h) ha (Bool.of_not_eq_true hT) hc hg he]; rfl
  | case11 n f env o os st rs env' hb ih =>
    rw [ih]
    show _ = (kont M st (liftExcept (env.bind (o.results.map (·.1)) rs.toDVals
      "an op names a number of results other than it gives") >>= fun env' =>
        Func.runOps M n f env' os)).run
    rw [hb]; rfl
  | case12 n f env o os st rs e hb =>
    show _ = (kont M st (liftExcept (env.bind (o.results.map (·.1)) rs.toDVals
      "an op names a number of results other than it gives") >>= fun env' =>
        Func.runOps M n f env' os)).run
    rw [hb]; exact (kont_error M st _).symm
  | case13 n f env o os st r => exact (kont_ub M r st).symm
  | case14 n f env o os st e => exact (kont_noOutcome M e st).symm
  | case15 n f env o os st w k =>
    exact (kont_choose M w st fun b => ((Cur.den n f env o os (k b)).denote M).run).symm
  | case16 n f env o args st h ih =>
    rw [ih]
    show _ = (kont M st (if sig o.op = f.results then pure (.ret (args.toDVals, n))
      else liftExcept (stuck "the function returns values of types other than its result types"))).run
    rw [ite_eq_left h]; rfl
  | case17 n f env o args st h =>
    show _ = (kont M st (if sig o.op = f.results then pure (.ret (args.toDVals, n))
      else liftExcept (stuck "the function returns values of types other than its result types"))).run
    rw [ite_eq_right h]; exact (kont_error M st _).symm
  | case18 n f env o args st i b env' hj ih =>
    rw [ih]
    show _ = (kont M st (liftExcept (f.jump env o.succs i) >>= fun x =>
      Func.runOps M n f x.2 x.1.body)).run
    rw [hj]; rfl
  | case19 n f env o args st i e hj =>
    show _ = (kont M st (liftExcept (f.jump env o.succs i) >>= fun x =>
      Func.runOps M n f x.2 x.1.body)).run
    rw [hj]; exact (kont_error M st _).symm
  | case20 n f env o args st r => exact (kont_ub M r st).symm
  | case21 n f env o args st e => exact (kont_noOutcome M e st).symm
  | case22 n f env o args st w k =>
    exact (kont_choose M w st fun b => ((Cur.ex n f env o args (k b)).denote M).run).symm
  | case23 vs k => rfl
  | case24 vs k fr st h env' hb ih =>
    rw [ih]
    show _ = (kont M st (fr.cont M (.ret (vs, k)))).run
    rw [Frame.cont, ite_eq_left h, hb]; rfl
  | case25 vs k fr st h e hb =>
    show _ = (kont M st (fr.cont M (.ret (vs, k)))).run
    rw [Frame.cont, ite_eq_left h, hb]; exact (kont_error M st _).symm
  | case26 vs k fr st h =>
    show _ = (kont M st (fr.cont M (.ret (vs, k)))).run
    rw [Frame.cont, ite_eq_right h]; exact (kont_error M st _).symm

end Proofs

end FirRef.Machine
