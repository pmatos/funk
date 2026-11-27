import Fir.Execution.MemoryFiniteExit
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
          | callRet hreg hargs => exact h hreg hargs
          | pickExh hreg hargs => exact h hreg hargs⟩
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
        exact Func.memOps_notExhausted_exit hfin hf hops henv hS hreg hargs hargs' hr hT hnu hnx
          fun env₁ env₁' os₁ S₁ S₁' => ih N (Nat.lt_succ_self N) f env₁ env₁' os₁ S₁ S₁' hf
      have hT' : isTerminator o.op = false := by simpa using hT
      cases hcs : callee? o.op with
      | none =>
        -- An op with no callee: finitely many outcomes.
        obtain ⟨LD, hLD⟩ := (hfin.1 o.op (.inr hcs) args').1 hT' S'
        obtain ⟨m, hm⟩ := List.exists_budget (L := LD)
          (Q := fun p m => DialectDenote.denote (m := StateT (Memories Mem unit) SetM) o.op args' S'
            (.ok p) → (o.results.map (·.1)).length = p.1.toDVals.length →
              ¬ (Func.memOps M' m f ((o.results.map (·.1)).zip p.1.toDVals ++ env') os
                p.2).run (.ok (.ok .fuelExhausted)))
          (fun _ _ _ hle h hp hl => Func.memOps_notExhausted_up hle (h hp hl))
          fun ⟨rs', S₁'⟩ _ => by
            by_cases hp : DialectDenote.denote (m := StateT (Memories Mem unit) SetM) o.op args' S'
              (.ok (rs', S₁'))
            case neg => exact ⟨0, fun h => absurd h hp⟩
            obtain ⟨e₀, he₀, hle⟩ := (hmo.1 (.inr hcs) args args' hr).1 hT' S S' hS _ hp
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
        | pickExh _ _ _ hc => simp_all
        | callExh _ _ _ hc => cases hc <;> simp_all
        | callRet _ _ _ hc => cases hc <;> simp_all
      | some c =>
        -- A call: finitely many callees, arguments and memories, each with a budget.
        obtain ⟨T, hTc⟩ := Func.MemCallsAt.cover hfin M' o args' S'
        obtain ⟨m, hm⟩ := List.exists_budget (L := T)
          (Q := fun t m => (∃ (n₀ n₀' : Nat) (ts : List d.Ty) (cargs' : HVector toType ts),
              Func.MemCallsAt M' o args' S' n₀ t.1 ts cargs' n₀' t.2.2.2 ∧
                cargs'.toDVals = t.2.1 ∧ n₀ - n₀' = t.2.2.1) →
            ¬ Func.CallRunsOut M' m f env' o os t.1 t.2.1 t.2.2.2)
          (fun _ _ _ hle h hw hx => by
            obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
            exact h hw hx.down)
          fun ⟨s, dvs', δ, S₁'⟩ _ => by
            by_cases hw : ∃ (n₀ n₀' : Nat) (ts : List d.Ty) (cargs' : HVector toType ts),
              Func.MemCallsAt M' o args' S' n₀ s ts cargs' n₀' S₁' ∧ cargs'.toDVals = dvs' ∧
                n₀ - n₀' = δ
            case neg => exact ⟨0, fun h => absurd h hw⟩
            obtain ⟨n₀, n₀', ts, cargs', hc', rfl, rfl⟩ := hw
            obtain ⟨cargs, S₁, hc₀, hcr, hS₁⟩ | ⟨hpc, r, hpu⟩ := hc'.source hr hS hcalls.2.2 hmo.2
            case inr =>
              exact absurd ⟨1, r, src (fun _ h => nomatch h)
                (.pickUB (n := 0) hreg hargs hT' hpc hpu)⟩ hnu
            have hle₀ := hc₀.le
            rcases Nat.lt_or_ge N (n₀ - n₀') with hlt | hfit
            · obtain ⟨hpc, hs⟩ := hc₀.picked_of_lt (by omega)
              exact absurd (src hexh (.pickExh hreg hargs hT' hpc hs (by omega))) hnx
            have hc := hc₀.at (N - (n₀ - n₀'))
            rw [Nat.sub_add_cancel hfit] at hc
            suffices h : ∃ m, ¬ Func.CallRunsOut M' m f env' o os s cargs'.toDVals S₁' from
              let ⟨m, hm⟩ := h
              ⟨m, fun _ => hm⟩
            cases hg' : M'.func? s with
            | none => exact ⟨0, fun ⟨_, _, h, _⟩ => by simp_all⟩
            | some g₀ =>
            cases hen' : g₀.enter cargs'.toDVals with
            | error _ => exact ⟨0, fun ⟨_, _, h, h', _⟩ => by simp_all⟩
            | ok p' =>
            have callUB : ∀ {g : Func d} {p : List (Operation d) × Env d} {N' : Nat} {r : String},
                M.func? s = some g → g.enter cargs.toDVals = .ok p →
                (Func.memCall M N' g p.2 p.1 S₁).run (.ub r) → False :=
              fun {_ _ N' r} hg hen h => hnu ⟨_, r, src (fun _ h => nomatch h)
                (.callUB hreg hargs hT' (hc₀.at N') hg hen h)⟩
            have callExh : ∀ {g : Func d} {p : List (Operation d) × Env d},
                M.func? s = some g → g.enter cargs.toDVals = .ok p →
                (Func.memCall M (N - (n₀ - n₀')) g p.2 p.1 S₁).run (.ok (.ok .fuelExhausted)) →
                  False :=
              fun {_ _} hg hen h => hnx (src hexh (.callExh hreg hargs hT' hc hg hen h))
            obtain ⟨n₁, hn₁⟩ : ∃ n₁, ¬ (Func.memCall M' n₁ g₀ p'.2 p'.1 S₁').run
                (.ok (.ok .fuelExhausted)) := by
              by_cases hsame : M'.func? s = M.func? s
              · have hg : M.func? s = some g₀ := hsame ▸ hg'
                obtain ⟨genv, hen, hgenv⟩ := Func.enter_isRefinedBy (HVector.toDVals_isRefinedBy hcr) hen'
                have hgf := hmono g₀ (List.mem_of_find?_eq_some hg)
                obtain ⟨n₁, h₁⟩ := ih (N - (n₀ - n₀')) (by omega) g₀ genv p'.2 p'.1 S₁.enter S₁'.enter
                  hgf (hgf.enter (p := (p'.1, genv)) hen) hgenv hS₁.enter
                  (fun ⟨_, _, h⟩ => callUB (p := (p'.1, genv)) hg hen (Func.memCall_ub_of_memOps h))
                  (fun h => callExh (p := (p'.1, genv)) hg hen (Func.memCall_exhausted_iff.2 h))
                exact ⟨n₁, fun h => h₁ (Func.memCall_exhausted_iff.1 h)⟩
              rcases hcalls.1 s with h | ⟨g, g', hg, hg'', bb⟩
              · exact absurd h hsame
              rw [hg''] at hg'
              cases hg'
              have hsig := bb.sig hen'
              have inv := fun {N x} => Func.memRunsFrom_run_cast (M := M) (args := cargs) (S := S₁)
                (N := N) (x := x) hsig
              by_cases hdiv : ∀ m, (g₀.memRunsFrom M' ((cargs'.cast hsig).cast bb.params.symm, S₁')
                m).outcomes .fuelExhausted
              case neg =>
                obtain ⟨m, hm⟩ := Classical.not_forall.1 hdiv
                exact ⟨m, fun h => hm (bb.target_run hen' hexh h)⟩
              exfalso
              obtain ⟨s₀, hs₀, hle⟩ := bb.refines _ _ S₁ S₁' (HVector.forall₂_cast hsig hcr) hS₁
                .fuelExhausted hdiv
              match s₀, hs₀, hle with
              | .ub r, ⟨N', hN'⟩, _ =>
                obtain ⟨p, hp, e, he, hx⟩ := inv (x := .ub r) (fun _ h => nomatch h) hN'
                match e, he, hx with
                | .ub _, he, rfl => exact callUB hg hp he
              | .fuelExhausted, hs₀, _ =>
                obtain ⟨p, hp, e, he, hx⟩ := inv (x := .ok (.ok .fuelExhausted))
                  (fun _ h => nomatch h) (hs₀ (N - (n₀ - n₀')))
                match e, he, hx with
                | .ok (.ok .fuelExhausted), he, _ => exact callExh hg hp he
              | .ret _, _, hle => exact hle.elim
            obtain ⟨LC, hLC⟩ := Func.memCall_finitelyManyRets hfin M' n₁ g₀ p'.2 p'.1 S₁'
            obtain ⟨m, hm⟩ := List.exists_budget (L := LC)
              (Q := fun (r : (List (DVal d) × Memories Mem unit) × Nat) m =>
                (Func.memCall M' n₁ g₀ p'.2 p'.1 S₁').run (.ok (.ok (.ret r))) →
                r.1.1.map (·.1) = returnTypes o.op → (o.results.map (·.1)).length = r.1.1.length →
                  ¬ (Func.memOps M' m f ((o.results.map (·.1)).zip r.1.1 ++ env') os r.1.2).run
                    (.ok (.ok .fuelExhausted)))
              (fun _ _ _ hle h hx hty hl => Func.memOps_notExhausted_up hle (h hx hty hl))
              fun ⟨⟨vs', T'⟩, k'⟩ _ => by
                by_cases hall : (Func.memCall M' n₁ g₀ p'.2 p'.1 S₁').run
                    (.ok (.ok (.ret ((vs', T'), k')))) ∧
                  vs'.map (·.1) = returnTypes o.op ∧ (o.results.map (·.1)).length = vs'.length
                case neg => exact ⟨0, fun hx hty hl => absurd ⟨hx, hty, hl⟩ hall⟩
                obtain ⟨hx, hty', hlen'⟩ := hall
                obtain ⟨g, p, hg, hen, hal⟩ := hcalls.callee_allowed hmono hg' hcr hS₁ hen'
                  (fun hgm hbm env env' h T T' hT e' he' =>
                    Func.memOps_allowed hmono hcalls _ g₀ env env' _ T T' hgm hbm h hT e' he')
                  hx (fun _ h => nomatch h) (fun h => nomatch h)
                rcases hal with ⟨_, _, h⟩ | ⟨N₁, ⟨vs, T⟩, k, h₁, hvs, hT₁⟩
                · exact (callUB hg hen h).elim
                obtain ⟨k₀, hk₀⟩ : ∃ k₀, (Func.memCall M (N - (n₀ - n₀')) g p.2 p.1 S₁).run
                    (.ok (.ok (.ret ((vs, T), k₀)))) := by
                  rcases Nat.le_total N₁ (N - (n₀ - n₀')) with hle | hle
                  · have ha := Func.memCall_ahead M N₁ (N - (n₀ - n₀') - N₁) g p.2 p.1 S₁
                    rw [Nat.add_sub_cancel' hle] at ha
                    exact ⟨_, ha.up_ret _ _ h₁⟩
                  · have ha := Func.memCall_ahead M (N - (n₀ - n₀')) (N₁ - (N - (n₀ - n₀'))) g
                      p.2 p.1 S₁
                    rw [Nat.add_sub_cancel' hle] at ha
                    rcases ha.down_ret _ _ h₁ with ⟨_, h⟩ | h
                    · exact ⟨_, h⟩
                    · exact (callExh hg hen h).elim
                have hk₀N := Func.memCall_left_le M (N - (n₀ - n₀')) g p.2 p.1 S₁ _ _ hk₀
                have hty := (DVals.types_eq_of_isRefinedBy hvs).trans hty'
                have hlen := hlen'.trans (DVals.length_eq_of_isRefinedBy hvs).symm
                obtain ⟨m, hm⟩ := ih k₀ (by omega) f _ _ os T T' hf hops'
                  (henv.zip_append _ hvs) hT₁
                  (fun ⟨N₂, r, h⟩ => hnu ⟨_, r, Func.memCall_cont hreg hargs hT' hc₀ hg hen hk₀ hty
                    hlen (x := .ub r) (fun _ h => nomatch h) (fun h => nomatch h) h⟩)
                  (fun h => hnx (src hexh (.callRet hreg hargs hT' hc hg hen hk₀ hty hlen
                    (by rwa [Nat.min_eq_left hk₀N]))))
                exact ⟨m, fun _ _ _ => hm⟩
            refine ⟨n₁ + m, fun ⟨g, p, hg, hen, h⟩ => ?_⟩
            rw [hg'] at hg
            cases hg
            rw [hen'] at hen
            cases hen
            rcases h with hx | ⟨vs', T', k', hx, hty', hlen', h⟩
            · exact Func.memCall_notExhausted_up (Nat.le_add_right n₁ m) hn₁ hx
            have hk' := Func.memCall_left_le M' (n₁ + m) _ _ _ _ _ _ hx
            rw [Nat.min_eq_left hk'] at h
            rcases (Func.memCall_ahead M' n₁ m _ _ _ _).down_ret _ _ hx with ⟨hmk, hx₁⟩ | hx₁
            · exact Func.memOps_notExhausted_up hmk (hm _ (hLC _ hx₁) hx₁ hty' hlen') h
            · exact hn₁ hx₁
        have out : ∀ (n' : Nat) (s : Name) (ts : List d.Ty) (cargs : HVector toType ts)
            (S₁ : Memories Mem unit), Func.MemCallsAt M' o args' S' (m + 1) s ts cargs n' S₁ →
            Func.CallRunsOut M' n' f env' o os s cargs.toDVals S₁ → False := fun n' _ _ _ _ hc hx => by
          obtain ⟨j, hj⟩ : ∃ j, n' = m + j := Nat.exists_eq_add_of_le (by have := hc.le; omega)
          rw [hj] at hx
          exact hm _ (hTc _ _ _ _ _ _ hc) ⟨_, _, _, _, hc, rfl, rfl⟩ hx.down
        refine ⟨m + 2, fun hx => ?_⟩
        cases (Func.memStepPath_iff hexh).1 hx with
        | goto _ _ hT'' => exact absurd hT'' hT
        | denote _ _ _ hc => rw [hc] at hcs; cases hcs
        | callExh _ hargs'' _ hc hg'' hen'' hx =>
          cases same hargs''
          exact out _ _ _ _ _ hc ⟨_, _, hg'', hen'', .inl hx⟩
        | callRet _ hargs'' _ hc hg'' hen'' hx hty' hlen' h =>
          cases same hargs''
          exact out _ _ _ _ _ hc ⟨_, _, hg'', hen'', .inr ⟨_, _, _, hx, hty', hlen', h⟩⟩
        | pickExh _ _ _ _ _ hn => cases hn

end Fir
