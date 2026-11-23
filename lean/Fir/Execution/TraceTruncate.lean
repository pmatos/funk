import Fir.Execution.TraceCut

/-!
# Truncating a traced run

A traced run with more fuel takes the same paths as one with less, further.
In the traced layer of marked traces, let every path of every op show
exactly one step, and let `W` exceed the length of every chain of calls of
the module by at least two. Then each path of a run of ops with `j` more
steps of fuel is _cut_ to a path of the run with fewer, from the same
environment and traced state:

* a return that leaves at least `j` steps is a return of the smaller run,
  with the same values, acts and traced state, that leaves `j` fewer; UB is
  UB of the smaller run, after the same acts;
* otherwise the smaller run runs out of fuel, _truncated_: after a marked
  trace that starts the longer path's, with at most as many steps as its
  budget _n_. If it shows less than the longer path, it has taken enough
  steps for its budget: `n ≤ W m + c`, where `m` is its number of steps and
  `c` the length of the chain of calls that its ops start. That is, it spent
  at most `W` steps of fuel on each step, and at most `c` on the calls
  before its first, and the longer path's next step comes before `W` more
  steps of fuel.

The proof follows the ways a step goes on, by strong induction on the
smaller budget. An op that runs by its own rule takes one step of fuel in
both runs and shows one step. A call spends one step of fuel and goes on in
its callee, one call further along the chain of its ops. When the callee
returns in both runs, the caller goes on in both with the steps they leave,
`j` apart; the fuel the callee spent is paced by its steps
(`Fir.Execution.TracePace`). When the callee returns only in the longer run,
the cut is in the callee: its truncated path shows all of the callee's acts
at most when the callee spent its fuel on its steps. A call whose callee is
picked (#235) takes two steps of fuel, after the step of its rule, and its
callees in the two runs are `j` apart too; when the shorter run has no step
left for the call, it runs out of fuel after the rule's step, which a
longer path that returns has gone past with fewer than `j` steps left.
-/

namespace Fir

open Memory

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem] {A : Type}
  [DialectDenote d (TraceM (Step A) (TraceState Mem unit))]
  [DialectExtCall d (TraceM (Step A) (TraceState Mem unit))] {M : Module d} {W : Nat}

/-- A way of ending of the traced layer of marked traces. -/
local notation "End" => TraceEnd (Step A) (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))

variable (A) in
/-- Each path of a traced run of ops with `j` more steps of fuel that is not
stuck is cut to a path of the run with `n`, from the same environment and
traced state, when every path of every op shows exactly one step and `W`
exceeds the length of every chain of calls of the module by at least two. -/
theorem Func.traceOps_cut (hone : OpsOneStep d A (TraceState Mem unit))
    (hW : ∀ os c, M.CallChain os c → c + 2 ≤ W) (hpos : 0 < W) (n : Nat) :
    ∀ (j : Nat) (f : Func d) (env : Env d) (os : List (Operation d)) (s : TraceState Mem unit)
      (e' : End), Func.traceOps (Step A) M (n + j) f env os s e' → TraceEnd.NotStuck e' →
      ∃ e, Func.traceOps (Step A) M n f env os s e ∧ e.Cut M W j n os e' := by
  have hpace := Func.traceOps_retPaced A hone hW
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro j f env os s e' he' hne
    match n, os, he' with
    | 0, os, he' =>
      refine ⟨_, Func.traceOps_zero.2 rfl, ?_⟩
      have htr : ∀ t : List (Step A), (t = [] ∨ ∃ c, M.CallChain os c) →
          TraceEnd.Truncated M W 0 os (.ok (.ok .fuelExhausted, [], s)) t := fun t ht =>
        ⟨[], s, rfl, List.nil_prefix, Nat.le_refl _,
          ht.imp (fun h => h.symm) fun ⟨c, hc⟩ => ⟨c, hc, Nat.zero_le _⟩⟩
      by_cases hch : ∃ c, M.CallChain os c
      · rcases e' with ⟨r, t⟩ | ⟨y, t, s'⟩
        · exact .inr (htr t (.inr hch))
        · rcases y with st | (⟨vs, k⟩ | _)
          · exact absurd rfl (hne st t s')
          · obtain ⟨hk, hp, -⟩ := hpace _ f env os s _ he' hne
            exact .inr ⟨by omega, htr t (.inr hch)⟩
          · exact htr t (.inr hch)
      · obtain ⟨s', rfl⟩ := Func.traceOps_silent _ f env os s (fun c hc => hch ⟨c, hc⟩) e' he' hne
        exact htr [] (.inl rfl)
    | n + 1, [], he' =>
      rw [Nat.add_right_comm] at he'
      exact absurd he' (Func.traceOps_nil hne)
    | n + 1, o :: os, he' =>
      rw [Nat.add_right_comm] at he'
      have ihn := ih n (Nat.lt_succ_self n)
      have mk : ∀ {x}, TraceEnd.NotStuck x → Func.TStepPath M n f env o os s x →
          Func.traceOps (Step A) M (n + 1) f env (o :: os) s x :=
        fun hx h => (Func.tStepPath_iff hx).2 h
      have hP := hpace _ f env (o :: os) s _ he' hne
      -- With no step left for the call, the rule that picks the callee runs out of fuel.
      have exh : ∀ {args : HVector toType (sig o.op)} {sym t₀ s₁} {e₁ : End},
          env.operands (sig o.op) o.operands = .ok args → o.ownsCoreRegion = false →
          isTerminator o.op = false → callee? o.op = some .picked →
          DialectDenote.pick (m := TraceM (Step A) (TraceState Mem unit)) o.op
            (M.callable (sig o.op).tail (returnTypes o.op)) args s (.ok (sym, t₀, s₁)) → n = 0 →
          TraceEnd.NotStuck e₁ → TraceEnd.RetPaced M W (n + j + 1) (o :: os) (e₁.after t₀) →
          (∀ vs k t s', e₁ = .ok (.ok (.ret (vs, k)), t, s') → 0 < Step.ticks t) →
          ∃ e, Func.traceOps (Step A) M (n + 1) f env (o :: os) s e ∧
            e.Cut M W j (n + 1) (o :: os) (e₁.after t₀) :=
        fun hargs hreg hT hpc hs hn hne₁ hp hpos₁ => by
          subst hn
          rw [Nat.zero_add] at hp
          have ht₀ := hone.2.2 _ _ _ _ _ hs
          exact ⟨_, mk (TraceEnd.notStuck_ok _ _ _) (.pickExh hreg hargs hT hpc hs rfl),
            TraceEnd.Cut.pickExh hpos (Module.callHead?_picked os hpc) ht₀ hne₁ hp hpos₁⟩
      cases (Func.tStepPath_iff hne).1 he' with
      | exitUB hreg hargs hT hos hx =>
        exact ⟨_, mk (TraceEnd.notStuck_error _ _) (.exitUB hreg hargs hT hos hx), .inl rfl⟩
      | ret hreg hargs hT hos hx hs =>
        refine ⟨_, mk (TraceEnd.notStuck_ok _ _ _) (.ret hreg hargs hT hos hx hs),
          .inl ⟨Nat.le_add_left _ _, ?_⟩⟩
        rw [Nat.add_sub_cancel]
      | goto hreg hargs hT hos hx hj h =>
        obtain ⟨e₁, h₁, hcut⟩ := ihn j _ _ _ _ _ h (TraceEnd.NotStuck.of_after hne)
        exact ⟨_, mk hcut.notStuck.after (.goto hreg hargs hT hos hx hj h₁),
          hcut.after_step hW (Module.callHead?_terminator os hT) ((hone.1 _ _ _).2 _ hx)⟩
      | denoteUB hreg hargs hT hc hx =>
        exact ⟨_, mk (TraceEnd.notStuck_error _ _) (.denoteUB hreg hargs hT hc hx), .inl rfl⟩
      | denote hreg hargs hT hc hx hlen h =>
        obtain ⟨e₁, h₁, hcut⟩ := ihn j _ _ _ _ _ h (TraceEnd.NotStuck.of_after hne)
        exact ⟨_, mk hcut.notStuck.after (.denote hreg hargs hT hc hx hlen h₁),
          hcut.after_step hW (Module.callHead?_noCallee os hc) ((hone.1 _ _ _).1 _ hx)⟩
      | extUB hreg hargs hT hc hg hd hx =>
        rcases hc.down (k := n) (j := j) with ⟨m, rfl, hc'⟩ | ⟨hn, hpc, hs⟩
        · exact ⟨_, mk (TraceEnd.notStuck_error _ _) (.extUB hreg hargs hT hc' hg hd hx), .inl rfl⟩
        · exact exh hargs hreg hT hpc hs hn (TraceEnd.notStuck_error _ _) hP
            (fun _ _ _ _ h => nomatch h)
      | @ext args sym ts cargs n'' t₀ s₁ vs t s' e₀ hreg hargs hT hc hg hd hx hty hlen h =>
        have ht : Step.ticks t = 1 := hone.2.1 _ _ _ _ _ hx
        rcases hc.down (k := n) (j := j) with ⟨m, rfl, hc'⟩ | ⟨hn, hpc, hs⟩
        case inr =>
          refine exh hargs hreg hT hpc hs hn hne.of_after hP fun vs' k t' s'' he => ?_
          rcases e₀ with _ | ⟨y, t₂, s₃⟩
          · cases he
          · simp only [TraceEnd.after, Except.ok.injEq, Prod.mk.injEq] at he
            obtain ⟨-, rfl, -⟩ := he
            rw [Step.ticks_append, ht]
            omega
        have hm := hc'.le
        obtain ⟨e₁, h₁, hcut⟩ := ih m (by omega) j _ _ _ _ _ h hne.of_after.of_after
        cases hc' with
        | fixed hc' =>
          refine ⟨_, mk hcut.notStuck.after.after (.ext hreg hargs hT (.fixed hc') hg hd hx hty hlen h₁),
            ?_⟩
          simp only [TraceEnd.after_nil]
          exact hcut.after_step hW (Module.callHead?_noFunc os hT hc' hg) ht
        | picked hpc hs =>
          have hos := Module.callHead?_picked (M := M) os hpc
          exact ⟨_, mk hcut.notStuck.after.after
            (.ext hreg hargs hT (.picked hpc hs) hg hd hx hty hlen h₁),
            (hcut.after_step hW hos ht).after_step hW hos (hone.2.2 _ _ _ _ _ hs)⟩
      | pickUB hreg hargs hT hpc hx =>
        exact ⟨_, mk (TraceEnd.notStuck_error _ _) (.pickUB hreg hargs hT hpc hx), .inl rfl⟩
      | @pickExh _ _ t₀ _ hreg hargs hT hpc hs hn =>
        obtain rfl : n = 0 := by omega
        have ht₀ : Step.ticks t₀ = 1 := hone.2.2 _ _ _ _ _ hs
        exact ⟨_, mk (TraceEnd.notStuck_ok _ _ _) (.pickExh hreg hargs hT hpc hs rfl),
          ⟨_, _, rfl, List.prefix_refl _, by omega, .inl rfl⟩⟩
      | callUB hreg hargs hT hc hg hen hx =>
        obtain ⟨e₁', h₁', he₁'⟩ := (TraceM.run_inFrame _ _ _).1 hx
        rcases e₁' with ⟨r₁, t₁⟩ | ⟨_, _, _⟩
        case ok => cases he₁'
        simp only [Except.map, Except.error.injEq] at he₁'
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he₁'
        rcases hc.down (k := n) (j := j) with ⟨m, rfl, hc'⟩ | ⟨hn, hpc, hs⟩
        case inr =>
          exact exh hargs hreg hT hpc hs hn (TraceEnd.notStuck_error _ _) hP
            (fun _ _ _ _ h => nomatch h)
        have hm := hc'.le
        obtain ⟨e₁, h₁, hcut⟩ := ih m (by omega) j _ _ _ _ _ h₁' (TraceEnd.notStuck_error _ _)
        rcases hcut with rfl | htr
        · exact ⟨_, mk (TraceEnd.notStuck_error _ _) (.callUB hreg hargs hT hc' hg hen
            ((TraceM.run_inFrame _ _ _).2 ⟨_, h₁, rfl⟩)), .inl rfl⟩
        cases hc' with
        | fixed hc' =>
          have htr' := htr.call (Module.callHead?_call os hT hc' hg hen) (List.prefix_refl _)
            (.inl rfl)
          obtain ⟨t₀, s₀, rfl, -⟩ := htr
          refine ⟨_, mk (TraceEnd.notStuck_ok _ _ _) (.callExh hreg hargs hT (.fixed hc') hg hen
            ((TraceM.run_inFrame _ _ _).2 ⟨_, h₁, rfl⟩)), ?_⟩
          simp only [TraceEnd.after_nil]
          exact .inr htr'
        | picked hpc hs =>
          have htr' := htr.picked hW (Module.callHead?_picked os hpc) (hone.2.2 _ _ _ _ _ hs)
            (List.prefix_refl _) (.inl rfl)
          obtain ⟨t₀, s₀, rfl, -⟩ := htr
          exact ⟨_, mk (TraceEnd.notStuck_ok _ _ _) (.callExh hreg hargs hT (.picked hpc hs) hg hen
            ((TraceM.run_inFrame _ _ _).2 ⟨_, h₁, rfl⟩)), .inr htr'⟩
      | callExh hreg hargs hT hc hg hen hx =>
        obtain ⟨e₁', h₁', he₁'⟩ := (TraceM.run_inFrame _ _ _).1 hx
        rcases e₁' with ⟨_, _⟩ | ⟨y, t₁, s₂⟩
        · cases he₁'
        simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at he₁'
        obtain ⟨rfl, rfl, -⟩ := he₁'
        rcases hc.down (k := n) (j := j) with ⟨m, rfl, hc'⟩ | ⟨hn, hpc, hs⟩
        case inr =>
          exact exh hargs hreg hT hpc hs hn (TraceEnd.notStuck_ok _ _ _) hP
            (fun _ _ _ _ h => nomatch h)
        have hm := hc'.le
        obtain ⟨e₁, h₁, htr⟩ := ih m (by omega) j _ _ _ _ _ h₁' (TraceEnd.notStuck_ok _ _ _)
        cases hc' with
        | fixed hc' =>
          have htr' := TraceEnd.Truncated.call htr (Module.callHead?_call os hT hc' hg hen)
            (List.prefix_refl _) (.inl rfl)
          obtain ⟨t₀, s₀, rfl, -⟩ := htr
          refine ⟨_, mk (TraceEnd.notStuck_ok _ _ _) (.callExh hreg hargs hT (.fixed hc') hg hen
            ((TraceM.run_inFrame _ _ _).2 ⟨_, h₁, rfl⟩)), ?_⟩
          simp only [TraceEnd.after_nil]
          exact htr'
        | picked hpc hs =>
          have htr' := htr.picked hW (Module.callHead?_picked os hpc) (hone.2.2 _ _ _ _ _ hs)
            (List.prefix_refl _) (.inl rfl)
          obtain ⟨t₀, s₀, rfl, -⟩ := htr
          exact ⟨_, mk (TraceEnd.notStuck_ok _ _ _) (.callExh hreg hargs hT (.picked hpc hs) hg hen
            ((TraceM.run_inFrame _ _ _).2 ⟨_, h₁, rfl⟩)), htr'⟩
      | @callRet args sym ts cargs n'' t₀ s₁ g body genv vs k₁ tc s₂ e₂' hreg hargs hT hc hg hen hx
          hty hlen h =>
        obtain ⟨e₁', h₁', he₁'⟩ := (TraceM.run_inFrame _ _ _).1 hx
        rcases e₁' with ⟨_, _⟩ | ⟨y, t₁, s₃⟩
        · cases he₁'
        simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at he₁'
        obtain ⟨rfl, rfl, rfl⟩ := he₁'
        obtain ⟨hk₁, hp₁, c₁, hc₁, hb₁⟩ := hpace _ _ _ _ _ _ h₁' (TraceEnd.notStuck_ok _ _ _)
        rw [Nat.min_eq_left (by omega : k₁ ≤ n'')] at h
        have hW₁ := hW _ _ hc₁
        rcases hc.down (k := n) (j := j) with ⟨m, rfl, hc'⟩ | ⟨hn, hpc, hs⟩
        case inr =>
          refine exh hargs hreg hT hpc hs hn hne.of_after hP fun vs' k t s' he => ?_
          rcases e₂' with _ | ⟨y₂, t₂, s₄⟩
          · cases he
          · simp only [TraceEnd.after, Except.ok.injEq, Prod.mk.injEq] at he
            obtain ⟨-, rfl, -⟩ := he
            rw [Step.ticks_append]
            omega
        have hm := hc'.le
        obtain ⟨e₁, h₁, hcut₁⟩ := ih m (by omega) j _ _ _ _ _ h₁' (TraceEnd.notStuck_ok _ _ _)
        cases hc' with
        | fixed hc' =>
          have hs := Module.callHead?_call os hT hc' hg hen
          rcases hcut₁ with ⟨hj, rfl⟩ | ⟨hk, htr⟩
          · -- The callee returns in both runs; the caller goes on with steps `j` apart.
            obtain ⟨hk₁', -, c₁', hc₁', hb₁'⟩ := hpace _ _ _ _ _ _ h₁ (TraceEnd.notStuck_ok _ _ _)
            have hW₁' := hW _ _ hc₁'
            replace hk₁' : k₁ - j + Step.ticks tc ≤ n := hk₁'
            rw [← Nat.sub_add_cancel hj] at h
            obtain ⟨e₂, h₂, hcut₂⟩ := ih (k₁ - j) (by omega) j _ _ _ _ _ h hne.of_after.of_after
            refine ⟨_, mk hcut₂.notStuck.after.after (.callRet hreg hargs hT (.fixed hc') hg hen
              ((TraceM.run_inFrame _ _ _).2 ⟨_, h₁, rfl⟩) hty hlen
              ((Nat.min_eq_left (by omega : k₁ - j ≤ n)).symm ▸ h₂)), ?_⟩
            simp only [TraceEnd.after_nil]
            have hbud : ∀ x, k₁ - j + 1 ≤ W * x + W →
                n + 1 ≤ W * Step.ticks tc + W * x + (c₁' + 1) := fun x hx => by omega
            have hcall := Module.CallChain.call hs hc₁'
            have hticks : Step.ticks tc + (k₁ - j) ≤ n + 1 := by omega
            rcases e₂' with ⟨r, t₂⟩ | ⟨y₂, t₂, s₃⟩
            · rcases hcut₂ with rfl | htr
              · exact .inl rfl
              · exact .inr (htr.after hW hticks hbud hcall)
            · rcases y₂ with st | (⟨vs₂, k₂⟩ | _)
              · exact hcut₂.elim
              · rcases hcut₂ with ⟨hj₂, rfl⟩ | ⟨hk₂, htr⟩
                · exact .inl ⟨hj₂, rfl⟩
                · exact .inr ⟨hk₂, htr.after hW hticks hbud hcall⟩
              · exact TraceEnd.Truncated.after hW hcut₂ hticks hbud hcall
          · -- The callee is cut: it ran out of fuel, its fuel spent on its steps.
            have htr' : ∀ t₂, TraceEnd.Truncated M W (n + 1) (o :: os)
                (e₁.map fun p => (p.1, p.2.1, { p.2.2 with mem := p.2.2.mem.exit })) (tc ++ t₂) :=
              fun t₂ => htr.call hs (List.prefix_append _ _) (.inr ⟨c₁, hc₁, by omega⟩)
            obtain ⟨t₀, s₀, rfl, -⟩ := htr
            refine ⟨_, mk (TraceEnd.notStuck_ok _ _ _) (.callExh hreg hargs hT (.fixed hc') hg hen
              ((TraceM.run_inFrame _ _ _).2 ⟨_, h₁, rfl⟩)), ?_⟩
            simp only [TraceEnd.after_nil]
            rcases e₂' with ⟨r, t₂⟩ | ⟨y₂, t₂, s₃⟩
            · exact .inr (htr' t₂)
            · rcases y₂ with st | (⟨vs₂, k₂⟩ | _)
              · exact absurd rfl (hne.of_after.of_after st t₂ s₃)
              · obtain ⟨hk₂, -⟩ := hpace _ _ _ _ _ _ h (TraceEnd.notStuck_ok _ _ _)
                exact .inr ⟨by omega, htr' t₂⟩
              · exact htr' t₂
        | picked hpc hs =>
          have hos := Module.callHead?_picked (M := M) os hpc
          have ht₀ : Step.ticks t₀ = 1 := hone.2.2 _ _ _ _ _ hs
          rcases hcut₁ with ⟨hj, rfl⟩ | ⟨hk, htr⟩
          · -- The callee returns in both runs; the caller goes on with steps `j` apart.
            obtain ⟨hk₁', -, c₁', hc₁', hb₁'⟩ := hpace _ _ _ _ _ _ h₁ (TraceEnd.notStuck_ok _ _ _)
            have hW₁' := hW _ _ hc₁'
            replace hk₁' : k₁ - j + Step.ticks tc ≤ m := hk₁'
            rw [← Nat.sub_add_cancel hj] at h
            obtain ⟨e₂, h₂, hcut₂⟩ := ih (k₁ - j) (by omega) j _ _ _ _ _ h hne.of_after.of_after
            refine ⟨_, mk hcut₂.notStuck.after.after (.callRet hreg hargs hT (.picked hpc hs) hg hen
              ((TraceM.run_inFrame _ _ _).2 ⟨_, h₁, rfl⟩) hty hlen
              ((Nat.min_eq_left (by omega : k₁ - j ≤ m)).symm ▸ h₂)), ?_⟩
            rw [TraceEnd.after_after, TraceEnd.after_after]
            have hbud : ∀ x, k₁ - j + 1 ≤ W * x + W →
                m + 1 + 1 ≤ W * Step.ticks (t₀ ++ tc) + W * x + 0 := fun x hx => by
              rw [Step.ticks_append, ht₀, Nat.mul_add, Nat.mul_one]
              omega
            have hcall : M.CallChain (o :: os) 0 := .stop hos
            have hticks : Step.ticks (t₀ ++ tc) + (k₁ - j) ≤ m + 1 + 1 := by
              rw [Step.ticks_append, ht₀]
              omega
            rcases e₂' with ⟨r, t₂⟩ | ⟨y₂, t₂, s₃⟩
            · rcases hcut₂ with rfl | htr
              · exact .inl rfl
              · exact .inr (htr.after hW hticks hbud hcall)
            · rcases y₂ with st | (⟨vs₂, k₂⟩ | _)
              · exact hcut₂.elim
              · rcases hcut₂ with ⟨hj₂, rfl⟩ | ⟨hk₂, htr⟩
                · exact .inl ⟨hj₂, rfl⟩
                · exact .inr ⟨hk₂, htr.after hW hticks hbud hcall⟩
              · exact TraceEnd.Truncated.after hW hcut₂ hticks hbud hcall
          · -- The callee is cut: it ran out of fuel, its fuel spent on its steps.
            have htr' : ∀ t₂, TraceEnd.Truncated M W (m + 1 + 1) (o :: os)
                (TraceEnd.after t₀
                  (e₁.map fun p => (p.1, p.2.1, { p.2.2 with mem := p.2.2.mem.exit })))
                (t₀ ++ (tc ++ t₂)) :=
              fun t₂ => htr.picked hW hos ht₀ (List.prefix_append _ _) (.inr ⟨c₁, hc₁, by omega⟩)
            obtain ⟨t₀', s₀, rfl, -⟩ := htr
            refine ⟨_, mk (TraceEnd.notStuck_ok _ _ _) (.callExh hreg hargs hT (.picked hpc hs) hg hen
              ((TraceM.run_inFrame _ _ _).2 ⟨_, h₁, rfl⟩)), ?_⟩
            rcases e₂' with ⟨r, t₂⟩ | ⟨y₂, t₂, s₃⟩
            · exact .inr (htr' t₂)
            · rcases y₂ with st | (⟨vs₂, k₂⟩ | _)
              · exact absurd rfl (hne.of_after.of_after st t₂ s₃)
              · obtain ⟨hk₂, -⟩ := hpace _ _ _ _ _ _ h (TraceEnd.notStuck_ok _ _ _)
                exact .inr ⟨by omega, htr' t₂⟩
              · exact htr' t₂

end Fir
