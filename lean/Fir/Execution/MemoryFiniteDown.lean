import Fir.Execution.MemoryFinite
import Fir.Execution.MemoryRefineDown

/-!
# Divergence with ops of finitely many outcomes

A target that diverges runs out of fuel at every budget, and the source
must then diverge too, or hit UB at some budget. The section on divergence
of the target with memory proves it when every black box's runs are bounded
by one budget, for every input at once. A callee's inputs are its arguments
and the memories it starts from, and there are infinitely many of those, so
each input may need a budget of its own, and the budgets may have no
largest.

When every op that runs by its own rule has finitely many outcomes, no one
budget is needed. This is König's lemma, with budgets for paths: the source
at a budget reaches finitely many inputs of each call, so finitely many
budgets serve. Take a source that never hits UB, and a budget _N_ at which
it does not run out of fuel. Then some budget of the target, from an
environment and memories that refine the source's, does not run out of
fuel either. The proof is by strong induction on _N_, for every function at
once and from every memories:

* an op that runs by its own rule goes on in finitely many ways in the
  target. Each is allowed by a way that the op goes on in the source, since
  the source hits no UB, and the rest of the source's run, at one step
  fewer, does not run out of fuel. The induction gives a budget for each,
  and the largest serves them all;
* a call of the same function in both runs its callee, which the induction
  covers at one step fewer. A call of a black box runs the target's
  function, which cannot diverge on the call's arguments and memories,
  since its source would then diverge or hit UB there; so it has a budget
  of its own. Either way the callee returns finitely many things at that
  budget, each allowed by a return of the source's callee at its budget
  (the section on every return and UB of the target with memory), after
  which the rest of the source's run does not run out of fuel. The
  induction gives a budget for each, and the callee's budget plus the
  largest of them serves the call.

A path that runs out of fuel at a budget runs out of fuel at each smaller
one, so a budget at which no path runs out of fuel serves every larger
budget too.
-/

namespace Fir

open SetM Memory

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (StateT (Memories Mem unit) SetM)] [TyRefinement d.Ty]

/-- From a budget `N` at which the source's run of ops with memory does not
run out of fuel, and when the source never hits UB, some budget of the
target's run of the same ops, from an environment and memories that refine
the source's, does not run out of fuel, when every call names the same
function in both modules or a black box, every op that runs by its own rule
has finitely many outcomes, and every terminator and every op with no callee
is monotone with memory, among the ops of the source module's functions, of
the function `f` that runs, and of the ops `os` it runs. -/
theorem Func.memOps_notExhausted_of_finite {M M' : Module d}
    (hmono : ∀ g ∈ M.funcs, g.MemOpsMonotone Mem unit) (hfin : OpsFinite d Mem unit)
    (hcalls : MemCallsRefined Mem unit M M') (N : Nat) :
    ∀ (f : Func d) (env env' : Env d) (os : List (Operation d)) (S S' : Memories Mem unit),
      f.MemOpsMonotone Mem unit → MemMonotoneOps Mem unit os → env.IsRefinedBy env' → S ⊑ S' →
      ¬ SomeUB (fun N => Func.memOps M N f env os S) →
      ¬ (Func.memOps M N f env os S).run (.ok (.ok .fuelExhausted)) →
      ∃ n, ¬ (Func.memOps M' n f env' os S').run (.ok (.ok .fuelExhausted)) := by
  have hexh : Ev.NotStuck (.ok (.ok .fuelExhausted) :
      Ev (Except Stuck (Result ((List (DVal d) × Memories Mem unit) × Nat)))) :=
    fun _ h => nomatch h
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro f env env' os S S' hf hops henv hS hnu hnx
    match N, os with
    | 0, _ => exact absurd (Func.run_memOps_zero.2 rfl) hnx
    | _ + 1, [] => exact ⟨1, Func.run_memOps_nil hexh⟩
    | N + 1, o :: os =>
      have src : ∀ {N' x}, Ev.NotStuck x → Func.MemStepPath M N' f env o os S x →
          (Func.memOps M (N' + 1) f env (o :: os) S).run x :=
        fun hx h => (Func.memStepPath_iff hx).2 h
      have hmo := hops o List.mem_cons_self
      have hops' : MemMonotoneOps Mem unit os := fun o' h => hops o' (List.mem_cons_of_mem _ h)
      have stuck : (∀ {args : HVector toType (sig o.op)}, o.ownsCoreRegion = false →
          env'.operands (sig o.op) o.operands = .ok args → False) →
          ∃ n, ¬ (Func.memOps M' n f env' (o :: os) S').run (.ok (.ok .fuelExhausted)) :=
        fun h => ⟨1, fun hx => by
          cases (Func.memStepPath_iff hexh).1 hx with
          | goto hreg hargs => exact h hreg hargs
          | denote hreg hargs => exact h hreg hargs
          | callExh hreg hargs => exact h hreg hargs
          | callRet hreg hargs => exact h hreg hargs⟩
      cases hreg : o.ownsCoreRegion with
      | true => exact stuck fun h _ => by simp_all
      | false =>
      cases hargs' : env'.operands (sig o.op) o.operands with
      | error _ => exact stuck fun _ h => by simp_all
      | ok args' =>
      have same : ∀ {a}, env'.operands (sig o.op) o.operands = .ok a → a = args' :=
        fun h => Except.ok.inj (h.symm.trans hargs')
      obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
      by_cases hT : isTerminator o.op = true
      · -- A terminator: finitely many exits.
        by_cases hos : os = []
        case neg =>
          exact ⟨1, fun hx => by
              cases (Func.memStepPath_iff hexh).1 hx with
              | goto _ _ _ hos' => exact hos hos'
              | denote _ _ hT' => simp_all
              | callExh _ _ hT' => simp_all
              | callRet _ _ hT' => simp_all⟩
        obtain ⟨LE, hLE⟩ := (hfin o.op (.inl hT) args').2 hT S'
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
                obtain ⟨e₀, he₀, hle⟩ := (hmo (.inl hT) args args' hr).2 hT S S' hS _ hp
                match e₀, he₀, hle with
                | .ub r, he₀, _ => exact absurd ⟨1, r, src (fun _ h => nomatch h)
                    (.exitUB hreg hargs hT hos he₀)⟩ hnu
                | .ok (_, S₁), he₀, ⟨rfl, hS₁⟩ =>
                  obtain ⟨env₁, hj₁, henv₁⟩ := henv.jump hj
                  obtain ⟨m, hm⟩ := ih N (Nat.lt_succ_self N) f env₁ q.2 q.1.body S₁ S₁' hf
                    (hf.jump hj₁) henv₁ hS₁
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
        | denote _ _ hT' => simp_all
        | callExh _ _ hT' => simp_all
        | callRet _ _ hT' => simp_all
      have hT' : isTerminator o.op = false := by simpa using hT
      cases hcs : callee? o.op with
      | none =>
        -- An op with no callee: finitely many outcomes.
        obtain ⟨LD, hLD⟩ := (hfin o.op (.inr hcs) args').1 hT' S'
        obtain ⟨m, hm⟩ := List.exists_budget (L := LD)
          (Q := fun p m => DialectDenote.denote (m := StateT (Memories Mem unit) SetM) o.op args' S'
            (.ok p) → (o.results.map (·.1)).length = p.1.toDVals.length →
              ¬ (Func.memOps M' m f ((o.results.map (·.1)).zip p.1.toDVals ++ env') os
                p.2).run (.ok (.ok .fuelExhausted)))
          (fun _ _ _ hle h hp hl => Func.memOps_notExhausted_up hle (h hp hl))
          fun ⟨rs', S₁'⟩ _ => by
            classical
            by_cases hp : DialectDenote.denote (m := StateT (Memories Mem unit) SetM) o.op args' S'
              (.ok (rs', S₁'))
            case neg => exact ⟨0, fun h => absurd h hp⟩
            obtain ⟨e₀, he₀, hle⟩ := (hmo (.inr hcs) args args' hr).1 hT' S S' hS _ hp
            match e₀, he₀, hle with
            | .ub r, he₀, _ => exact absurd ⟨1, r, src (fun _ h => nomatch h)
                (.denoteUB hreg hargs hT' hcs he₀)⟩ hnu
            | .ok (rs, S₁), he₀, ⟨hrs, hS₁⟩ =>
              have hvs := HVector.toDVals_isRefinedBy hrs
              by_cases hlen : (o.results.map (·.1)).length = rs.toDVals.length
              case neg =>
                exact ⟨0, fun _ hl => absurd (hl.trans (DVals.length_eq_of_isRefinedBy hvs).symm)
                  hlen⟩
              obtain ⟨m, hm⟩ := ih N (Nat.lt_succ_self N) f _ _ os S₁ S₁' hf hops'
                (henv.zip_append _ hvs) hS₁
                (fun ⟨N', r, h⟩ => hnu ⟨N' + 1, r, src (fun _ h => nomatch h)
                  (.denote hreg hargs hT' hcs he₀ hlen h)⟩)
                (fun h => hnx (src hexh (.denote hreg hargs hT' hcs he₀ hlen h)))
              exact ⟨m, fun _ _ => hm⟩
        refine ⟨m + 1, fun hx => ?_⟩
        cases (Func.memStepPath_iff hexh).1 hx with
        | goto _ _ hT'' => simp_all
        | denote _ hargs'' _ _ hx hl h =>
          cases same hargs''
          exact hm _ (hLD _ hx) hx hl h
        | callExh _ _ _ hc => simp_all
        | callRet _ _ _ hc => simp_all
      | some s =>
        -- A call: a budget for the callee, then one for each of its finitely many returns.
        cases hg' : M'.func? s with
        | none => exact ⟨1, fun hx => by cases (Func.memStepPath_iff hexh).1 hx <;> simp_all⟩
        | some g₀ =>
        cases hen' : g₀.enter args'.toDVals with
        | error _ => exact ⟨1, fun hx => by cases (Func.memStepPath_iff hexh).1 hx <;> simp_all⟩
        | ok p' =>
        have callUB : ∀ {g : Func d} {p : List (Operation d) × Env d} {N' : Nat} {r : String},
            M.func? s = some g → g.enter args.toDVals = .ok p →
            (Func.memCall M N' g p.2 p.1 S).run (.ub r) → False :=
          fun {_ _ N' r} hg hen h =>
            hnu ⟨N' + 1, r, src (fun _ h => nomatch h) (.callUB hreg hargs hT' hcs hg hen h)⟩
        have callExh : ∀ {g : Func d} {p : List (Operation d) × Env d},
            M.func? s = some g → g.enter args.toDVals = .ok p →
            (Func.memCall M N g p.2 p.1 S).run (.ok (.ok .fuelExhausted)) → False :=
          fun {_ _} hg hen h => hnx (src hexh (.callExh hreg hargs hT' hcs hg hen h))
        obtain ⟨n₁, hn₁⟩ : ∃ n₁, ¬ (Func.memCall M' n₁ g₀ p'.2 p'.1 S').run
            (.ok (.ok .fuelExhausted)) := by
          by_cases hsame : M'.func? s = M.func? s
          · have hg : M.func? s = some g₀ := hsame ▸ hg'
            obtain ⟨genv, hen, hgenv⟩ :=
              Func.enter_isRefinedBy (HVector.toDVals_isRefinedBy hr) hen'
            have hgf := hmono g₀ (List.mem_of_find?_eq_some hg)
            obtain ⟨n₁, h₁⟩ := ih N (Nat.lt_succ_self N) g₀ genv p'.2 p'.1 S.enter S'.enter hgf
              (hgf.enter (p := (p'.1, genv)) hen) hgenv hS.enter
              (fun ⟨_, _, h⟩ => callUB (p := (p'.1, genv)) hg hen (Func.memCall_ub_of_memOps h))
              (fun h => callExh (p := (p'.1, genv)) hg hen (Func.memCall_exhausted_iff.2 h))
            exact ⟨n₁, fun h => h₁ (Func.memCall_exhausted_iff.1 h)⟩
          rcases hcalls s with h | ⟨g, g', hg, hg'', bb⟩
          · exact absurd h hsame
          rw [hg''] at hg'
          cases hg'
          have hsig := bb.sig hen'
          have inv := fun {N x} => Func.memRunsFrom_run_cast (M := M) (args := args) (S := S)
            (N := N) (x := x) hsig
          classical
          by_cases hdiv : ∀ m, (g₀.memRunsFrom M' ((args'.cast hsig).cast bb.params.symm, S')
            m).outcomes .fuelExhausted
          case neg =>
            obtain ⟨m, hm⟩ := Classical.not_forall.1 hdiv
            exact ⟨m, fun h => hm (bb.target_run hen' hexh h)⟩
          exfalso
          obtain ⟨s₀, hs₀, hle⟩ := bb.refines _ _ S S' (HVector.forall₂_cast hsig hr) hS
            .fuelExhausted hdiv
          match s₀, hs₀, hle with
          | .ub r, ⟨N', hN'⟩, _ =>
            obtain ⟨p, hp, e, he, hx⟩ := inv (x := .ub r) (fun _ h => nomatch h) hN'
            match e, he, hx with
            | .ub _, he, rfl => exact callUB hg hp he
          | .fuelExhausted, hs₀, _ =>
            obtain ⟨p, hp, e, he, hx⟩ := inv (x := .ok (.ok .fuelExhausted)) (fun _ h => nomatch h)
              (hs₀ N)
            match e, he, hx with
            | .ok (.ok .fuelExhausted), he, _ => exact callExh hg hp he
          | .ret _, _, hle => exact hle.elim
        obtain ⟨LC, hLC⟩ := Func.memCall_finitelyManyRets hfin M' n₁ g₀ p'.2 p'.1 S'
        obtain ⟨m, hm⟩ := List.exists_budget (L := LC)
          (Q := fun (r : (List (DVal d) × Memories Mem unit) × Nat) m =>
            (Func.memCall M' n₁ g₀ p'.2 p'.1 S').run (.ok (.ok (.ret r))) →
            r.1.1.map (·.1) = returnTypes o.op → (o.results.map (·.1)).length = r.1.1.length →
              ¬ (Func.memOps M' m f ((o.results.map (·.1)).zip r.1.1 ++ env') os r.1.2).run
                (.ok (.ok .fuelExhausted)))
          (fun _ _ _ hle h hx hty hl => Func.memOps_notExhausted_up hle (h hx hty hl))
          fun ⟨⟨vs', T'⟩, k'⟩ _ => by
            classical
            by_cases hall : (Func.memCall M' n₁ g₀ p'.2 p'.1 S').run (.ok (.ok (.ret ((vs', T'), k'))))
              ∧ vs'.map (·.1) = returnTypes o.op ∧ (o.results.map (·.1)).length = vs'.length
            case neg => exact ⟨0, fun hx hty hl => absurd ⟨hx, hty, hl⟩ hall⟩
            obtain ⟨hx, hty', hlen'⟩ := hall
            obtain ⟨g, p, hg, hen, hal⟩ := hcalls.callee_allowed hmono hg' hr hS hen'
              (fun hgm hbm env env' h T T' hT e' he' =>
                Func.memOps_allowed hmono hcalls _ g₀ env env' _ T T' hgm hbm h hT e' he')
              hx (fun _ h => nomatch h) (fun h => nomatch h)
            rcases hal with ⟨_, _, h⟩ | ⟨N₁, ⟨vs, T⟩, k, h₁, hvs, hT₁⟩
            · exact (callUB hg hen h).elim
            obtain ⟨k₀, hk₀⟩ : ∃ k₀, (Func.memCall M N g p.2 p.1 S).run
                (.ok (.ok (.ret ((vs, T), k₀)))) := by
              rcases Nat.le_total N₁ N with hle | hle
              · have ha := Func.memCall_ahead M N₁ (N - N₁) g p.2 p.1 S
                rw [Nat.add_sub_cancel' hle] at ha
                exact ⟨_, ha.up_ret _ _ h₁⟩
              · have ha := Func.memCall_ahead M N (N₁ - N) g p.2 p.1 S
                rw [Nat.add_sub_cancel' hle] at ha
                rcases ha.down_ret _ _ h₁ with ⟨_, h⟩ | h
                · exact ⟨_, h⟩
                · exact (callExh hg hen h).elim
            have hk₀N := Func.memCall_left_le M N g p.2 p.1 S _ _ hk₀
            have hty := (DVals.types_eq_of_isRefinedBy hvs).trans hty'
            have hlen := hlen'.trans (DVals.length_eq_of_isRefinedBy hvs).symm
            obtain ⟨m, hm⟩ := ih k₀ (Nat.lt_succ_of_le hk₀N) f _ _ os T T' hf hops'
              (henv.zip_append _ hvs) hT₁
              (fun ⟨N₂, r, h⟩ => hnu ⟨_, r, Func.memCall_cont hreg hargs hT' hcs hg hen hk₀ hty hlen
                (x := .ub r) (fun _ h => nomatch h) (fun h => nomatch h) h⟩)
              (fun h => hnx (src hexh (.callRet hreg hargs hT' hcs hg hen hk₀ hty hlen
                (by rwa [Nat.min_eq_left hk₀N]))))
            exact ⟨m, fun _ _ _ => hm⟩
        refine ⟨n₁ + m + 1, fun hx => ?_⟩
        cases (Func.memStepPath_iff hexh).1 hx with
        | goto _ _ hT'' => simp_all
        | denote _ _ _ hc => simp_all
        | callExh _ hargs'' _ hc hg'' hen'' hx =>
          cases same hargs''
          rw [hc] at hcs
          cases hcs
          rw [hg''] at hg'
          cases hg'
          rw [hen''] at hen'
          cases hen'
          exact Func.memCall_notExhausted_up (Nat.le_add_right n₁ m) hn₁ hx
        | callRet _ hargs'' _ hc hg'' hen'' hx hty' hlen' h =>
          cases same hargs''
          rw [hc] at hcs
          cases hcs
          rw [hg''] at hg'
          cases hg'
          rw [hen''] at hen'
          cases hen'
          rename_i vs' T' k'
          have hk' := Func.memCall_left_le M' (n₁ + m) _ _ _ _ _ _ hx
          rw [Nat.min_eq_left hk'] at h
          rcases (Func.memCall_ahead M' n₁ m _ _ _ _).down_ret _ _ hx with ⟨hmk, hx₁⟩ | hx₁
          · exact Func.memOps_notExhausted_up hmk (hm _ (hLC _ hx₁) hx₁ hty' hlen') h
          · exact hn₁ hx₁

end Fir
