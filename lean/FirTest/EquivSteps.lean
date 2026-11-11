import Fir

/-!
The unfolding lemmas of the equivalence experiment of #282, which
`FirTest.Equiv` and `FirTest.EquivNsw` use. They turn a question about the
behaviour of two functions into a question about the values they return,
which a bitvector tactic can then answer.

A function of the set monad's interpreter is a set of the ways a run may
end, at each fuel budget. `bv_decide` sees none of that: it decides
statements about bitvectors. Four groups of lemmas close the gap.

* _One step at a time._ `run_of_enter` starts a run at the entry block.
  `runOps_denote` runs one op that is not a terminator and calls no
  function, when its rule gives one result with no choice and no UB:
  the run goes on with one step less, with the op's results bound.
  `runOps_ret` runs a `ret`, which returns its operands. `operands_cons`
  looks up an op's operands. Each lemma is proved once, for every dialect,
  so a proof about a straight-line function only names its ops.
* _One budget is enough._ `observable_of_runs` says that when a run
  returns `v` at one budget, its observable behaviour is that return and
  nothing else. It rests on fuel monotonicity, which holds for every
  function (`Func.fuelMonotone`), and on the bridge lemma
  `observable_eq_at`.
* _Refinement of such functions is refinement of their values._
  `FuncRuns.isRefinedBy_iff_of_returns` says that when the source and the
  target return `vs a` and `vt a` on each argument vector `a`, the target
  refines the source exactly when `vs a ⊑ vt a` for every `a`. It is an
  iff, so it proves refinement and refutes it alike.
  `obs_isRefinedBy_iff` takes one returned `iN` to `PoisonOr` refinement.
* _With memory._ No lemma is new here: the runs with memory of a core
  function are its runs, at every naming of memories, since core ops touch
  no memory (`Func.memRuns_eq`), so each result carries over.
-/

namespace FirTest.EquivSteps

open Fir Core SetM

/-- A computation that succeeds, lifted into the run's monad, is `pure`. -/
theorem liftExcept_ok {ε α : Type} (a : α) :
    (liftExcept (Except.ok a : Except ε α) : ExceptT ε SetM α) = pure a := rfl

/-- `liftExcept_ok`, with the success written as `pure`. -/
theorem liftExcept_pure {ε α : Type} (a : α) :
    (liftExcept (pure a : Except ε α) : ExceptT ε SetM α) = pure a := rfl

section

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty]

/-- The operands `x :: xs`, of types `t :: ts`: the value of `x`, which has
type `t`, then those of `xs`. -/
theorem operands_cons {env : Env d} {t : d.Ty} {ts : List d.Ty} {x : Name} {xs : List Name}
    {v : ⟦t⟧} {vs : HVector toType ts} (hx : env.lookup x = some ⟨t, v⟩)
    (hs : env.operands ts xs = .ok vs) : env.operands (t :: ts) (x :: xs) = .ok (.cons v vs) := by
  simp [Env.operands, Env.value, hx, hs]
  rfl

variable [DialectSignature d] [DialectCall d] [DialectDenote d SetM]

/-- A run of a function, once it has entered its entry block: the run of the
block's ops, which returns its values. -/
theorem run_of_enter {M : Module d} {f : Func d} {args : HVector toType (f.params.map (·.2))}
    {body : List (Operation d)} {env : Env d} (hen : f.enter args.toDVals = .ok (body, env))
    (fuel : Nat) :
    f.run (m := SetM) M args fuel = (Func.runOps (m := SetM) M fuel f env body >>= fun r =>
      match r with
      | .ret (vs, _) => pure (.ret vs)
      | .fuelExhausted => pure .fuelExhausted) := by
  simp [Func.run, hen, inFrame_setM, liftExcept_ok]
  rfl

/-- One op that is not a terminator and calls no function, whose rule gives
the results `rs` with no choice and no UB: the run binds them and goes on
with one step less. -/
theorem runOps_denote {M : Module d} {n : Nat} {f : Func d} {env : Env d} {o : Operation d}
    {os : List (Operation d)} {args : HVector toType (sig o.op)}
    {rs : HVector toType (returnTypes o.op)}
    (hreg : o.ownsCoreRegion = false) (hargs : env.operands (sig o.op) o.operands = .ok args)
    (hT : isTerminator o.op = false) (hc : callee? o.op = none)
    (hd : DialectDenote.denote (m := SetM) o.op args = pure rs)
    (hlen : (o.results.map (·.1)).length = rs.toDVals.length) :
    Func.runOps (m := SetM) M (n + 1) f env (o :: os) =
      Func.runOps (m := SetM) M n f ((o.results.map (·.1)).zip rs.toDVals ++ env) os := by
  rw [Func.runOps]
  simp [hreg, hargs, hT, hc, hd, Env.bind, hlen, liftExcept_ok, liftExcept_pure]

/-- A terminator that returns, the last op of its block: the run returns
its operands, with the steps left. -/
theorem runOps_ret {M : Module d} {n : Nat} {f : Func d} {env : Env d} {o : Operation d}
    {args : HVector toType (sig o.op)}
    (hreg : o.ownsCoreRegion = false) (hargs : env.operands (sig o.op) o.operands = .ok args)
    (hT : isTerminator o.op = true) (he : DialectDenote.exit (m := SetM) o.op args = pure .ret)
    (hsig : sig o.op = f.results) :
    Func.runOps (m := SetM) M (n + 1) f env [o] = pure (.ret (args.toDVals, n)) := by
  rw [Func.runOps]
  simp [hreg, hargs, hT, he, hsig, liftExcept_ok]

end

/-- A fuel-monotone run that returns `v` at some budget, and does nothing
else there, has one observable outcome: that return. -/
theorem observable_of_runs {O : Type} {run : Nat → Run O} (hm : FuelMonotone run) {N : Nat}
    {v : O} (h : run N = (pure (.ret v) : ExceptT Stuck SetM (Result O))) (t : Outcome O) :
    observable run t ↔ t = .ret v := by
  have hN : ¬ (run N).outcomes .fuelExhausted := by
    rw [h]
    intro h'
    cases h'
  rw [observable_eq_at hm hN, h]
  cases t <;> simp [Run.outcomes, pure, ExceptT.pure, ExceptT.mk]

/-- The target refines the source, when each returns one value on each
argument vector, exactly when the source's value is refined by the
target's on every argument vector. -/
theorem FuncRuns.isRefinedBy_iff_of_returns {A O : Type} [HRefinement O O]
    {src tgt : FuncRuns A O} {vs vt : A → O}
    (hms : ∀ a, FuelMonotone (src a)) (hmt : ∀ a, FuelMonotone (tgt a))
    (hs : ∀ a, ∃ N, src a N = (pure (.ret (vs a)) : ExceptT Stuck SetM (Result O)))
    (ht : ∀ a, ∃ N, tgt a N = (pure (.ret (vt a)) : ExceptT Stuck SetM (Result O))) :
    src ⊑ tgt ↔ ∀ a, vs a ⊑ vt a := by
  have obs_s a := (hs a).elim fun _ h => observable_of_runs (hms a) h
  have obs_t a := (ht a).elim fun _ h => observable_of_runs (hmt a) h
  constructor
  · intro h a
    obtain ⟨s, hs', hst⟩ := h a (.ret (vt a)) ((obs_t a _).2 rfl)
    rw [obs_s a] at hs'
    subst hs'
    exact hst
  · intro h a t ht'
    rw [obs_t a] at ht'
    subst ht'
    exact ⟨.ret (vs a), (obs_s a _).2 rfl, h a⟩

/-- One returned `iN` refines another exactly when its value does. -/
theorem obs_isRefinedBy_iff {w : Nat} (a b : PoisonOr (BitVec w)) :
    ([⟨i w, a⟩] : Core.Obs) ⊑ ([⟨i w, b⟩] : Core.Obs) ↔ a ⊑ b := by
  constructor
  · rintro ⟨⟨_, h⟩, _⟩
    exact h
  · intro h
    exact ⟨⟨rfl, h⟩, trivial⟩

end FirTest.EquivSteps
