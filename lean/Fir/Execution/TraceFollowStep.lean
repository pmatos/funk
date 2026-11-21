import Fir.Execution.TraceFollow

/-!
# One move of the target, followed by the source

For each move of the target, a source configuration that follows the target's
allows the stream that the move puts before what the target shows after it, or
follows with a move whose acts the target's refine (`TCfg.Follows.step`). The
cases are those of `Fir.Execution.TraceFollow`. The one case where the source
does not follow is a call of a black box whose callee diverges in the target:
the target's callee then shows the stream at every budget, so its traced runs
diverge (`TShows.toObservable`), and the black box gives the source's callee
UB, or divergence whose stream the target's refines, which the source's call
shows at every budget too.
-/

namespace Fir

open Memory

variable {A : Type} [HRefinement A A] {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (TraceM (Step A) (TraceState Mem unit))] [TyRefinement d.Ty] {M M' : Module d}

/-- A source configuration that follows a target's, for each move of the
target, allows the stream that the move puts before a closed stream that the
target shows after it at every budget, or follows with a move whose acts the
target's refine, when every call names the same function in both modules or a
traced black box, and the ops of the source module's functions that run by
their own rule are monotone. -/
theorem TCfg.Follows.step (hone : OpsOneStep d A (TraceState Mem unit))
    (hmono : ∀ g ∈ M.funcs, g.TraceOpsMonotone (Step A) (TraceState Mem unit))
    (hcalls : TraceCallsRefined A Mem unit M M') {c c' c'₁ : TCfg d Mem unit}
    {t' : List (Step A)} {F' : Nat} (hc : c.Follows A c') (hmv : TCfg.Move A M' c' c'₁ t' F')
    {T₁ : Nat → Option A} {K₁ : Nat → Nat} (hshow : TShows (c'₁.exh A M') T₁ K₁)
    (hcl : Stream.Closed T₁) :
    c.Allows M (Stream.cat (Step.actsOf t') T₁) ∨
      ∃ c₁ t F, TCfg.Move A M c c₁ t F ∧ c₁.Follows A c'₁ ∧ Step.actsOf t ⊑ Step.actsOf t' := by
  rcases c with ⟨f, env, os, s⟩
  obtain ⟨hf, hos, henv, hs, hfm, hops⟩ := hc
  dsimp only at hf hos henv hs hfm hops
  have ub : ∀ {N r t₀}, TCfg.ub A M ⟨f, env, os, s⟩ N r t₀ → List.IsRefinedPrefix t₀ t' →
      TCfg.Allows M ⟨f, env, os, s⟩ (Stream.cat (Step.actsOf t') T₁) := fun hu hle =>
    .inl ⟨_, _, _, hu, Stream.ShowsRefined.of_prefix (Step.actsOf_isRefinedPrefix hle) T₁⟩
  have ubActs : ∀ {N r t₀}, TCfg.ub A M ⟨f, env, os, s⟩ N r t₀ →
      List.IsRefinedPrefix (Step.actsOf t₀) (Step.actsOf t') →
      TCfg.Allows M ⟨f, env, os, s⟩ (Stream.cat (Step.actsOf t') T₁) := fun hu hle =>
    .inl ⟨_, _, _, hu, Stream.ShowsRefined.of_prefix hle T₁⟩
  have mk : ∀ {N : Nat} {o : Operation d} {os' : List (Operation d)} {e}, os = o :: os' →
      Func.TStepPath M N f env o os' s e → TraceEnd.NotStuck e →
      Func.traceOps (Step A) M (N + 1) f env os s e := fun hos' h hne =>
    hos' ▸ (Func.tStepPath_iff hne).2 h
  cases hmv with
  | @denote _ _ o os' s' s'₁ args' rs' t' hreg hargs' hT hcn hx' hlen' =>
    subst hf hos
    obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
    have hmo := hops o List.mem_cons_self (.inr hcn)
    obtain ⟨e, he, hle⟩ := ((hmo args args' hr).1 hT) s s' hs _ hx'
    rcases e with ⟨r, t₀⟩ | ⟨rs, t, s₁⟩
    · exact .inl (ub (mk (N := 0) rfl (.denoteUB hreg hargs hT hcn he) (TraceEnd.notStuck_error _ _)) hle)
    · obtain ⟨hrs, ht, hs₁⟩ := hle
      have hvs := HVector.toDVals_isRefinedBy hrs
      exact .inr ⟨_, t, 1, .denote hreg hargs hT hcn he
        (hlen'.trans (DVals.length_eq_of_isRefinedBy hvs).symm),
        ⟨rfl, rfl, henv.zip_append _ hvs, hs₁, hfm, fun o' h => hops o' (List.mem_cons_of_mem _ h)⟩,
        Step.actsOf_isRefinedBy ht⟩
  | @goto _ _ env'₁ o os' s' s'₁ args' i t' b hreg hargs' hT hos' hx' hj' =>
    subst hf hos
    obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
    have hmo := hops o List.mem_cons_self (.inl hT)
    obtain ⟨e, he, hle⟩ := ((hmo args args' hr).2 hT) s s' hs _ hx'
    rcases e with ⟨r, t₀⟩ | ⟨x, t, s₁⟩
    · exact .inl (ub (mk (N := 0) rfl (.exitUB hreg hargs hT hos' he) (TraceEnd.notStuck_error _ _)) hle)
    · obtain ⟨rfl, ht, hs₁⟩ := hle
      obtain ⟨env₁, hj, henv₁⟩ := henv.jump hj'
      exact .inr ⟨_, t, 1, .goto hreg hargs hT hos' he hj,
        ⟨rfl, rfl, henv₁, hs₁, hfm, hfm.jump hj⟩, Step.actsOf_isRefinedBy ht⟩
  | @ret _ _ o os' s' s'₁ args' sym g₀ body' genv' U k' vs' t' hreg hargs' hT hcs hg' hen' hx' hty' hlen' =>
    subst hf hos
    obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
    obtain ⟨g, p, hg, hen, hm⟩ := hcalls.callee_allowed hmono hg' hr hs (p' := (_, _)) hen'
      (fun hgm hbm env₀ env₀' h t₀ t₀' ht e₀ he₀ =>
        Func.traceOps_tAllowed hmono hcalls _ _ env₀ env₀' _ t₀ t₀' hgm hbm h ht e₀ he₀) hx' trivial
    rcases hm with ⟨N, r, mt, hN, hle⟩ | ⟨N, vs, k, t, s₁, hN, hvs, ht, hs₁⟩
    · exact .inl (ubActs (mk rfl (.callUB hreg hargs hT hcs hg hen hN) (TraceEnd.notStuck_error _ _)) hle)
    · exact .inr ⟨_, t, N + 1, .ret hreg hargs hT hcs hg hen hN
        ((DVals.types_eq_of_isRefinedBy hvs).trans hty')
        (hlen'.trans (DVals.length_eq_of_isRefinedBy hvs).symm),
        ⟨rfl, rfl, henv.zip_append _ hvs, hs₁, hfm, fun o' h => hops o' (List.mem_cons_of_mem _ h)⟩, ht⟩
  | @enter _ _ o os' s' args' sym g' body' genv' hreg hargs' hT hcs hg' hen' =>
    subst hf hos
    obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
    rcases hcalls sym with hsame | ⟨g, g'', hg, hg'', bb⟩
    · have hg : M.func? sym = some g' := hsame ▸ hg'
      obtain ⟨genv, hen, hgenv⟩ := Func.enter_isRefinedBy (HVector.toDVals_isRefinedBy hr) hen'
      have hgm := hmono g' (List.mem_of_find?_eq_some hg)
      exact .inr ⟨_, [], 1, .enter hreg hargs hT hcs hg hen,
        ⟨rfl, rfl, hgenv, TraceState.IsRefinedBy.enter hs, hgm, hgm.enter hen⟩, trivial⟩
    have hgg : g' = g'' := Option.some.inj (hg'.symm.trans hg'')
    subst hgg
    -- A call of a black box whose callee diverges in the target.
    refine .inl ?_
    rw [show Step.actsOf ([] : List (Step A)) = [] from rfl, Stream.cat_nil]
    have hsig := bb.sig hen'
    have hcast : ((args.cast hsig) : HVector toType _).toDVals = args.toDVals := HVector.toDVals_cast _ _
    have hcast' : ((args'.cast hsig).cast bb.params.symm : HVector toType _).toDVals =
        args'.toDVals := by rw [HVector.toDVals_cast, HVector.toDVals_cast]
    have hen'' : g'.enter ((args'.cast hsig).cast bb.params.symm).toDVals = .ok (body', genv') :=
      hcast' ▸ hen'
    have hshow' := hshow.congr (TCfg.exh_iff_traceFrom hen'')
    obtain ⟨t₁, ht₁, hdiv, hact⟩ := hshow'.toObservable hcl
    obtain ⟨t₀, ht₀, hle⟩ := bb.refines _ _ s s' (HVector.forall₂_cast hsig hr) hs t₁ ht₁
    match t₀, ht₀, hle with
    | .ub tr r, ⟨N, mt, hN, htr⟩, hle =>
      obtain ⟨body, genv, hen, h⟩ := Func.traceFrom_ub_iff.1 hN
      rw [hcast] at hen
      refine .inl ⟨N + 1, r, mt, mk rfl (.callUB hreg hargs hT hcs hg hen h)
        (TraceEnd.notStuck_error _ _), fun i a ha => ?_⟩
      obtain ⟨b, hb, hab⟩ := hle i a (htr ▸ ha)
      exact ⟨b, hact i ▸ hb, hab⟩
    | .ret _ _, _, hle =>
      match t₁, hdiv with
      | .diverge _, _ | .reacts _, _ => exact (hle : False).elim
    | .diverge tr₀, ht₀, hle | .reacts T₀, ht₀, hle =>
      obtain ⟨K, hK⟩ := TShows.ofObservable ht₀ trivial
      obtain ⟨mt₀, hmt₀, -⟩ := hK 0
      obtain ⟨body, genv, -, hen, -⟩ := Func.traceFrom_exhausted_iff.1 hmt₀
      have hen₀ := hen
      rw [hcast] at hen₀
      have hK' := hK.congr fun n mt => (TCfg.exh_iff_traceFrom (M := M) hen n mt).symm
      have := TShows.step ((TCfg.Move.enter (M := M) (f := f) (env := env) (os := os')
        (s := s) hreg hargs hT hcs hg hen₀).tStep hone) hK'
      rw [show Step.actsOf ([] : List (Step A)) = [] from rfl, Stream.cat_nil] at this
      refine .inr ⟨_, _, this, fun i => ?_⟩
      rw [← hact i]
      exact TOutcome.stream_isRefinedBy (by exact trivial) hdiv hle i

end Fir
