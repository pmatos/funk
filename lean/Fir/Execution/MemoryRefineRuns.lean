import Fir.Execution.MemoryRefineDown

/-!
# A call with memory on arguments and memories that refine others

The first of the two refinement theorems for whole functions with memory:
on arguments that refine others, and from memories that refine others, a
function's observable behaviour from given memories, the memories it ends
with included, refines its behaviour on those others. It holds for every
function of every module, calls and recursion included, when the
terminators and the ops with no callee of the function and of the module's
functions are monotone with memory. A function's runs with memory start
from the empty memories, which refine themselves, so on arguments that
refine others, its runs with memory refine its runs with memory on those
others.

Both function-level theorems with memory are instances of one, as for runs
in the set monad (the section on a call on arguments that refine others):
a function of a source module, and the same function of a target module
whose calls name the same functions as the source's, or black boxes with
memory. Each outcome of the target is allowed by one of the source:

* a return or UB at some budget, by the section on every return and UB of
  the target with memory;
* divergence: if the source hits UB at some budget, it allows anything; if
  not, then for each budget of the source, the target runs out of fuel at a
  large enough budget, on a path that the source allows at its budget, by
  the section on divergence of the target with memory, so the source runs
  out of fuel there. That section asks that the runs of each black box's
  target be bounded by one budget; the section on divergence with ops of
  finitely many outcomes asks for none.

The run of a function runs its entry block's ops in a frame, as a call does,
so each outcome of its run is one of the run of those ops, allowed as a
callee's is.
-/

namespace Fir

open SetM Memory

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (StateT (Memories Mem unit) SetM)] [TyRefinement d.Ty]

/-- Every path of the target's run of ops with memory that runs out of
fuel or returns, at a budget of at least `(bound + 1) * (N + 1)`, is allowed
by the source's run at `N`, from environments and memories of which the
target's refine the source's, when every call names the same function in
both modules or a black box whose target's runs are bounded by `bound`, and
every terminator and every op with no callee is monotone with memory, among
the ops of the source module's functions, of the function `f` that runs,
and of the ops `os` it runs. -/
theorem Func.memOps_allowedBelow {M M' : Module d}
    (hmono : ∀ g ∈ M.funcs, g.MemOpsMonotone Mem unit) {bound : Nat}
    (hcalls : MemCallsRefined Mem unit M M') (hbnd : MemCallsBounded Mem unit M M' bound)
    (n : Nat) :
    ∀ (f : Func d) (env env' : Env d) (os : List (Operation d)) (S S' : Memories Mem unit)
      (N : Nat), f.MemOpsMonotone Mem unit → MemMonotoneOps Mem unit os → env.IsRefinedBy env' →
      S ⊑ S' → (bound + 1) * (N + 1) ≤ n →
      ∀ e', (Func.memOps M' n f env' os S').run e' →
        MemAllowedBelow (bound + 1) (fun N => Func.memOps M N f env os S) N e' := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f env env' os S S' N hf hops henv hS hN e' he'
    classical
    by_cases hgood : Ev.NotStuck e' ∧ ∀ r, e' ≠ .ub r
    case neg => exact MemAllowedBelow.of_not hgood
    obtain ⟨hne, hnub⟩ := hgood
    have hpos : 0 < (bound + 1) * (N + 1) := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
    have hub : ∀ {N : Nat} {r : String} {o : Operation d} {os : List (Operation d)},
        Func.MemStepPath M N f env o os S (.ub r) →
        (Func.memOps M (N + 1) f env (o :: os) S).run (.ub r) :=
      fun {_ r _ _} h => (Func.memStepPath_iff (e := .ub r) (fun _ h => nomatch h)).2 h
    match n, os, N, hops, he' with
    | 0, _, _, _, _ => omega
    | _ + 1, _, 0, _, _ => exact MemAllowedBelow.of_exhausted (Func.run_memOps_zero.2 rfl) _
    | n + 1, [], _ + 1, _, he' => exact absurd he' (Func.run_memOps_nil hne)
    | n + 1, o :: os, N₀ + 1, hops, he' =>
      have hb : bound + (bound + 1) * (N₀ + 1) ≤ n := by rw [Nat.mul_succ] at hN; omega
      have hb' : (bound + 1) * (N₀ + 1) ≤ n := by omega
      have ihn := ih n (Nat.lt_succ_self n)
      have hmo := hops o List.mem_cons_self
      have hops' : MemMonotoneOps Mem unit os := fun o' h => hops o' (List.mem_cons_of_mem _ h)
      have step : ∀ {c : Nat → ExceptT Stuck SetM
            (Result ((List (DVal d) × Memories Mem unit) × Nat))},
          (∀ N x, Ev.NotStuck x → (c N).run x → Func.MemStepPath M N f env o os S x) →
          MemAllowedBelow (bound + 1) c N₀ e' →
          MemAllowedBelow (bound + 1) (fun N => Func.memOps M N f env (o :: os) S) (N₀ + 1) e' :=
        fun hcp => MemAllowedBelow.of_step
          (fun x hx h => (Func.memStepPath_iff hx).2 (hcp _ x hx h))
          (fun ⟨N, r, h⟩ => ⟨N + 1, r, hub (hcp N _ (fun _ h => nomatch h) h)⟩)
      cases (Func.memStepPath_iff hne).1 he' with
      | exitUB _ _ _ _ _ => exact absurd rfl (hnub _)
      | denoteUB _ _ _ _ _ => exact absurd rfl (hnub _)
      | callUB _ _ _ _ _ _ _ => exact absurd rfl (hnub _)
      | ret hreg hargs' hT hos hx hs =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmo (.inl hT) args _ hr).2 hT S S' hS _ hx
        match e₀, he₀, hle with
        | .ub r, he₀, _ =>
          exact MemAllowedBelow.of_someUB ⟨1, r, hub (.exitUB hreg hargs hT hos he₀)⟩ _
        | .ok (_, S₁), he₀, ⟨rfl, hS₁⟩ =>
          exact .inr (.inr ⟨_, N₀,
            (Func.memStepPath_iff (e := .ok (.ok (.ret ((args.toDVals, S₁), N₀))))
              (fun _ h => nomatch h)).2 (.ret hreg hargs hT hos he₀ hs),
            ⟨HVector.toDVals_isRefinedBy hr, hS₁⟩, hb'⟩)
      | goto hreg hargs' hT hos hx hj he =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmo (.inl hT) args _ hr).2 hT S S' hS _ hx
        match e₀, he₀, hle with
        | .ub r, he₀, _ =>
          exact MemAllowedBelow.of_someUB ⟨1, r, hub (.exitUB hreg hargs hT hos he₀)⟩ _
        | .ok (_, S₁), he₀, ⟨rfl, hS₁⟩ =>
          obtain ⟨env₁, hj₁, henv₁⟩ := henv.jump hj
          exact step (fun N x _ h => .goto hreg hargs hT hos he₀ hj₁ h)
            (ihn _ _ _ _ _ _ _ hf (hf.jump hj) henv₁ hS₁ hb' _ he)
      | denote hreg hargs' hT hc hx hlen' he =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmo (.inr hc) args _ hr).1 hT S S' hS _ hx
        match e₀, he₀, hle with
        | .ub r, he₀, _ =>
          exact MemAllowedBelow.of_someUB ⟨1, r, hub (.denoteUB hreg hargs hT hc he₀)⟩ _
        | .ok (rs, S₁), he₀, ⟨hrs, hS₁⟩ =>
          have hvs := HVector.toDVals_isRefinedBy hrs
          have hlen := hlen'.trans (DVals.length_eq_of_isRefinedBy hvs).symm
          exact step (fun N x _ h => .denote hreg hargs hT hc he₀ hlen h)
            (ihn _ _ _ _ _ _ _ hf hops' (henv.zip_append _ hvs) hS₁ hb' _ he)
      | callExh hreg hargs' hT hc hg' hen' hx =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨g, p, hg, hen, hm⟩ := hcalls.callee_allowedBelow hbnd hmono hg' hr hS
          (p' := (_, _)) hen' hb (fun hgm hbm env env' h T T' hT e' he' =>
            ihn _ env env' _ T T' N₀ hgm hbm h hT hb' e' he') hx
          (fun _ h => nomatch h) (fun _ h => nomatch h)
        rcases hm with h | ⟨N, r, h⟩
        · exact MemAllowedBelow.of_exhausted ((Func.memStepPath_iff (e := .ok (.ok .fuelExhausted))
            (fun _ h => nomatch h)).2 (.callExh hreg hargs hT hc hg hen h)) _
        · exact MemAllowedBelow.of_someUB ⟨N + 1, r, hub (.callUB hreg hargs hT hc hg hen h)⟩ _
      | callRet hreg hargs' hT hc hg' hen' hx hty' hlen' he =>
        rename_i vs' T' k'
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨g, p, hg, hen, hm⟩ := hcalls.callee_allowedBelow hbnd hmono hg' hr hS
          (p' := (_, _)) hen' hb (fun hgm hbm env env' h T T' hT e' he' =>
            ihn _ env env' _ T T' N₀ hgm hbm h hT hb' e' he') hx
          (fun _ h => nomatch h) (fun _ h => nomatch h)
        rcases hm with h | ⟨N, r, h⟩ | ⟨⟨vs, T⟩, k, hx₁, ⟨hvs, hT₁⟩, hk⟩
        · exact MemAllowedBelow.of_exhausted ((Func.memStepPath_iff (e := .ok (.ok .fuelExhausted))
            (fun _ h => nomatch h)).2 (.callExh hreg hargs hT hc hg hen h)) _
        · exact MemAllowedBelow.of_someUB ⟨N + 1, r, hub (.callUB hreg hargs hT hc hg hen h)⟩ _
        have hty := (DVals.types_eq_of_isRefinedBy hvs).trans hty'
        have hlen := hlen'.trans (DVals.length_eq_of_isRefinedBy hvs).symm
        have hk'n := Func.memCall_left_le M' n _ _ _ _ _ _ hx
        have hkN := Func.memCall_left_le M N₀ _ _ _ _ _ _ hx₁
        rw [Nat.min_eq_left hk'n] at he
        have hm := ih k' (Nat.lt_succ_of_le hk'n) _ _ _ _ _ _ k hf hops' (henv.zip_append _ hvs)
          hT₁ hk _ he
        refine MemAllowedBelow.of_step (fun x hx h => (Func.memStepPath_iff hx).2
          (.callRet hreg hargs hT hc hg hen hx₁ hty hlen (by rwa [Nat.min_eq_left hkN]))) ?_ hm
        rintro ⟨N₂, r, h⟩
        exact ⟨_, r, Func.memCall_cont hreg hargs hT hc hg hen hx₁ hty hlen
          (x := .ub r) (fun _ h => nomatch h) (fun h => nomatch h) h⟩

/-- A function's behaviour from given memories in the target module, on
arguments that refine others and from memories that refine others, refines
its behaviour from those others in the source module, the memories they end
with included, when every call names the same function in both modules or a
black box with memory, and every terminator and every op with no callee of
the function and of the source module's functions is monotone with
memory, and the runs of each black box's target are bounded by one
budget. -/
theorem Func.memRunsFrom_isRefinedBy_of_calls {M M' : Module d}
    (hmono : ∀ g ∈ M.funcs, g.MemOpsMonotone Mem unit) {bound : Nat}
    (hcalls : MemCallsRefined Mem unit M M') (hbnd : MemCallsBounded Mem unit M M' bound)
    (f : Func d) (hf : f.MemOpsMonotone Mem unit)
    {a a' : HVector toType (f.params.map (·.2))} (ha : a.Forall₂ TyRefinement.IsRefinedBy a')
    {S S' : Memories Mem unit} (hS : S ⊑ S') :
    observable (f.memRunsFrom M (a, S)) ⊑ observable (f.memRunsFrom M' (a', S')) := by
  have start : ∀ {p' : List (Operation d) × Env d}, f.enter a'.toDVals = .ok p' →
      ∃ genv, f.enter a.toDVals = .ok (p'.1, genv) ∧ genv.IsRefinedBy p'.2 :=
    fun hen' => Func.enter_isRefinedBy (HVector.toDVals_isRefinedBy ha) hen'
  have back : ∀ {p : List (Operation d) × Env d} {N : Nat}
      {e : Ev (Except Stuck (Result ((List (DVal d) × Memories Mem unit) × Nat)))},
      Ev.NotStuck e.dropLeft → f.enter a.toDVals = .ok p →
      (Func.memCall M N f p.2 p.1 S).run e → (f.memRunsFrom M (a, S) N) e.dropLeft :=
    fun hne hen h => (Func.memRunsFrom_run hne).2 ⟨_, hen, _, h, rfl⟩
  have up : ∀ {p' : List (Operation d) × Env d}, f.enter a'.toDVals = .ok p' → ∀ {genv : Env d},
      genv.IsRefinedBy p'.2 → ∀ n e', (Func.memCall M' n f p'.2 p'.1 S').run e' →
        MemAllowed (fun N => Func.memCall M N f genv p'.1 S) e' :=
    fun {_} hen' {_} henv n _ he' => Func.memCall_allowed (fun e₀ he₀ => Func.memOps_allowed hmono hcalls n
      f _ _ _ _ _ hf (hf.enter hen') henv hS.enter e₀ he₀) he'
  intro t ht
  match t, ht with
  | .ret (vs', T'), ⟨n, hn⟩ =>
    obtain ⟨p', hen', e', he', hx⟩ :=
      (Func.memRunsFrom_run (x := .ok (.ok (.ret (vs', T')))) (fun _ h => nomatch h)).1 hn
    match e', he', hx with
    | .ok (.ok (.ret (_, k'))), he', rfl =>
      obtain ⟨genv, hen, henv⟩ := start hen'
      rcases up hen' henv n _ he' with ⟨N, r, h⟩ | ⟨N, ⟨vs, T⟩, k, h, hle⟩
      · exact ⟨.ub r, ⟨N, back (e := .ub r) (fun _ h => nomatch h) hen h⟩, trivial⟩
      · exact ⟨.ret (vs, T), ⟨N, back (e := .ok (.ok (.ret ((vs, T), k)))) (fun _ h => nomatch h)
          hen h⟩, hle⟩
  | .ub r', ⟨n, hn⟩ =>
    obtain ⟨p', hen', e', he', hx⟩ :=
      (Func.memRunsFrom_run (x := .ub r') (fun _ h => nomatch h)).1 hn
    match e', he', hx with
    | .ub _, he', rfl =>
      obtain ⟨genv, hen, henv⟩ := start hen'
      obtain ⟨N, r, h⟩ := up hen' henv n _ he'
      exact ⟨.ub r, ⟨N, back (e := .ub r) (fun _ h => nomatch h) hen h⟩, trivial⟩
  | .fuelExhausted, ht =>
    classical
    by_cases hU : ∃ N r, (f.memRunsFrom M (a, S) N).outcomes (.ub r)
    · obtain ⟨N, r, h⟩ := hU
      exact ⟨.ub r, ⟨N, h⟩, trivial⟩
    refine ⟨.fuelExhausted, fun N => ?_, trivial⟩
    obtain ⟨p', hen', e', he', hx⟩ := (Func.memRunsFrom_run (x := .ok (.ok .fuelExhausted))
      (fun _ h => nomatch h)).1 (ht ((bound + 1) * (N + 1)))
    match e', he', hx with
    | .ok (.ok .fuelExhausted), he', _ =>
      obtain ⟨genv, hen, henv⟩ := start hen'
      have hm := Func.memCall_allowedBelow (fun e₀ he₀ => Func.memOps_allowedBelow hmono hcalls hbnd _
        f _ _ _ _ _ N hf (hf.enter hen') henv hS.enter (Nat.le_refl _) e₀ he₀) he'
      rcases hm with h | ⟨N', r, h⟩
      · exact back (e := .ok (.ok .fuelExhausted)) (fun _ h => nomatch h) hen h
      · exact absurd ⟨N', r, back (e := .ub r) (fun _ h => nomatch h) hen h⟩ hU

/-- Refined arguments and memories: a function's behaviour from memories
that refine others, on arguments that refine others, a poison by any value,
refines its behaviour from those others, the memories they end with
included, in every module, calls and recursion included, when every
terminator and every op with no callee of the function and of the module's
functions is monotone with memory. -/
theorem Func.memRunsFrom_args_isRefinedBy (M : Module d)
    (hmono : ∀ g ∈ M.funcs, g.MemOpsMonotone Mem unit) (f : Func d) (hf : f.MemOpsMonotone Mem unit)
    {a a' : HVector toType (f.params.map (·.2))} (ha : a.Forall₂ TyRefinement.IsRefinedBy a')
    {S S' : Memories Mem unit} (hS : S ⊑ S') :
    observable (f.memRunsFrom M (a, S)) ⊑ observable (f.memRunsFrom M (a', S')) :=
  Func.memRunsFrom_isRefinedBy_of_calls hmono (bound := 0) (fun _ => .inl rfl)
    (fun _ _ _ h => absurd rfl h) f hf ha hS


end Fir
