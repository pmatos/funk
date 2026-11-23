import Fir.Execution.MemoryFinite
import Fir.Execution.MemoryRefineDown

/-!
# A terminator's exits, with a budget

The terminator case of `Func.memOps_notExhausted_of_finite`
(`Fir.Execution.MemoryFiniteDown`): a terminator of finitely many exits,
monotone with memory, whose source run never hits UB and does not run out
of fuel, has a budget at which the target's run, from an environment and
memories that refine the source's, does not run out of fuel, when the run
of each block it may jump to has one.
-/

namespace Fir

open SetM Memory

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (StateT (Memories Mem unit) SetM)] [TyRefinement d.Ty]

/-- A terminator of the ops `o :: os` whose source run with memory never hits
UB and does not run out of fuel at `N + 1` has a budget at which the
target's run of the same ops does not run out of fuel, from an environment
and memories that refine the source's, when its exits have finitely many
outcomes and are monotone with memory, and the run at `N` of each block it
may jump to has such a budget (`ih`). -/
theorem Func.memOps_notExhausted_exit {M M' : Module d} (hfin : OpsFinite d Mem unit) {N : Nat}
    {f : Func d} {env env' : Env d} {o : Operation d} {os : List (Operation d)}
    {S S' : Memories Mem unit} {args args' : HVector toType (sig o.op)}
    (hf : f.MemOpsMonotone Mem unit) (hops : MemMonotoneOps Mem unit (o :: os))
    (henv : env.IsRefinedBy env') (hS : S ⊑ S') (hreg : o.ownsCoreRegion = false)
    (hargs : env.operands (sig o.op) o.operands = .ok args)
    (hargs' : env'.operands (sig o.op) o.operands = .ok args')
    (hr : args.Forall₂ TyRefinement.IsRefinedBy args') (hT : isTerminator o.op = true)
    (hnu : ¬ SomeUB (fun N => Func.memOps M N f env (o :: os) S))
    (hnx : ¬ (Func.memOps M (N + 1) f env (o :: os) S).run (.ok (.ok .fuelExhausted)))
    (ih : ∀ (env env' : Env d) (os : List (Operation d)) (S S' : Memories Mem unit),
      MemMonotoneOps Mem unit os → env.IsRefinedBy env' → S ⊑ S' →
      ¬ SomeUB (fun N => Func.memOps M N f env os S) →
      ¬ (Func.memOps M N f env os S).run (.ok (.ok .fuelExhausted)) →
      ∃ n, ¬ (Func.memOps M' n f env' os S').run (.ok (.ok .fuelExhausted))) :
    ∃ n, ¬ (Func.memOps M' n f env' (o :: os) S').run (.ok (.ok .fuelExhausted)) := by
  have hexh : Ev.NotStuck (.ok (.ok .fuelExhausted) :
      Ev (Except Stuck (Result ((List (DVal d) × Memories Mem unit) × Nat)))) :=
    fun _ h => nomatch h
  have src : ∀ {N' x}, Ev.NotStuck x → Func.MemStepPath M N' f env o os S x →
      (Func.memOps M (N' + 1) f env (o :: os) S).run x :=
    fun hx h => (Func.memStepPath_iff hx).2 h
  have same : ∀ {a}, env'.operands (sig o.op) o.operands = .ok a → a = args' :=
    fun h => Except.ok.inj (h.symm.trans hargs')
  by_cases hos : os = []
  case neg =>
    exact ⟨1, fun hx => by
        cases (Func.memStepPath_iff hexh).1 hx with
        | goto _ _ _ hos' => exact hos hos'
        | denote _ _ hT' => simp_all
        | pickExh _ _ hT' => simp_all
        | callExh _ _ hT' => simp_all
        | callRet _ _ hT' => simp_all⟩
  obtain ⟨LE, hLE⟩ := (hfin.1 o.op (.inl hT) args').2 hT S'
  obtain ⟨m, hm⟩ := List.exists_budget (L := LE)
    (Q := fun p m => DialectDenote.exit (m := StateT (Memories Mem unit) SetM) o.op args' S'
      (.ok p) → ∀ i blk env₁', p.1 = .goto i → f.jump env' o.succs i = .ok (blk, env₁') →
        ¬ (Func.memOps M' m f env₁' blk.body p.2).run (.ok (.ok .fuelExhausted)))
    (fun _ _ _ hle h hp i blk env₁' hi hj => Func.memOps_notExhausted_up hle (h hp i blk env₁' hi hj))
    fun ⟨x', S₁'⟩ _ => by
      classical
      by_cases hp : DialectDenote.exit (m := StateT (Memories Mem unit) SetM) o.op args' S'
        (.ok (x', S₁'))
      case neg => exact ⟨0, fun h => absurd h hp⟩
      cases x' with
      | ret => exact ⟨0, fun _ _ _ _ h => nomatch h⟩
      | goto i =>
        cases hj : f.jump env' o.succs i with
        | error _ => exact ⟨0, fun _ _ _ _ hi h => by cases hi; simp_all⟩
        | ok q =>
          obtain ⟨e₀, he₀, hle⟩ := ((hops o List.mem_cons_self).1 (.inl hT) args args' hr).2 hT S S' hS _ hp
          match e₀, he₀, hle with
          | .ub r, he₀, _ => exact absurd ⟨1, r, src (fun _ h => nomatch h)
              (.exitUB hreg hargs hT hos he₀)⟩ hnu
          | .ok (_, S₁), he₀, ⟨rfl, hS₁⟩ =>
            obtain ⟨env₁, hj₁, henv₁⟩ := henv.jump hj
            obtain ⟨m, hm⟩ := ih env₁ q.2 q.1.body S₁ S₁' (hf.jump hj₁) henv₁ hS₁
              (fun ⟨N', r, h⟩ => hnu ⟨N' + 1, r, src (fun _ h => nomatch h)
                (.goto hreg hargs hT hos he₀ hj₁ h)⟩)
              (fun h => hnx (src hexh (.goto hreg hargs hT hos he₀ hj₁ h)))
            refine ⟨m, fun _ i' blk env₁' hi h => ?_⟩
            cases hi
            rw [hj] at h
            cases h
            exact hm
  refine ⟨m + 1, fun hx => ?_⟩
  cases (Func.memStepPath_iff hexh).1 hx with
  | goto _ hargs'' _ _ hx hj h =>
    cases same hargs''
    exact hm _ (hLE _ hx) hx _ _ _ rfl hj h
  | pickExh _ _ hT' => simp_all
  | denote _ _ hT' => simp_all
  | callExh _ _ hT' => simp_all
  | callRet _ _ hT' => simp_all

end Fir
