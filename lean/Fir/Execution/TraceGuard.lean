import Fir.Execution.TraceMoves
import Fir.Execution.TraceBlackBox

/-!
# Guards: the source path that a proof of refinement picks

A proof that a target's traced run refines a source's follows the target op
by op. At each op the source's monotone rule gives an outcome that allows
the target's: an existential, so the source's path is the one the proof
picks. An external call of the core is monotone only where the two calls
let escape the same allocations, in the same order (the human's rulings of
2026-11-21 and 2026-11-22 on #239, Q4 to Q6), and whether they do depends
on that path. So the condition under which refinement holds binds the
source's path, through a _guard_ (`TCfg.Guard`): a set of pairs of
configurations, the source's and the target's, closed in three ways.

* _Next steps._ When the target goes on by a step of its frame, an op by
  its own rule, a jump, an external call or a call whose callee returns
  (`TCfg.Next`), and the source has such a step that ends matched with the
  target's (`TCfg.Matched`), with acts that the target's refine, the
  source has one that ends in a pair of the set.
* _Calls that enter the same callee._ When the target enters a callee that
  both modules run, and the source has a call to it on arguments that the
  target's refine, the source has one whose entry into the callee is
  paired with the target's in the set.
* _External calls._ When the target calls an external declaration, and the
  source has a call to it on arguments that the target's refine, the
  source has one where the two calls agree.

Each clause only says which of the source's steps to take; none says that
one exists, so a guard restates no conclusion of the proofs that use it.
Where the two calls always agree, as in a dialect whose external calls show
no event, every set of pairs is a guard (`TCfg.Guard.always`).

A step of a frame that the source takes goes on as the source's run of the
ops after it, so a path of the step's next configuration that the target's
path allows gives one of the configuration (`TCfg.Next.tAllowed`).
-/

namespace Fir

open Memory

variable {A : Type} {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (TraceM (Step A) (TraceState Mem unit))]
  [DialectExtCall d (TraceM (Step A) (TraceState Mem unit))] {M : Module d}

variable (A) in
/-- A step of a configuration that stays in its frame, after the marked trace
`t` and with `F` steps of fuel: an op that runs by its own rule, with one of
its outcomes; a call of an external declaration, with one of the
external-call rule's outcomes; a terminator that jumps; or a call whose
callee returns at the budget `U`. They are the moves (`TCfg.Move`) other
than entering a callee. -/
inductive TCfg.Next (M : Module d) : TCfg d Mem unit → TCfg d Mem unit → List (Step A) → Nat → Prop
  | denote {f : Func d} {env : Env d} {o : Operation d} {os : List (Operation d)}
      {s s₁ : TraceState Mem unit} {args : HVector toType (sig o.op)}
      {rs : HVector toType (returnTypes o.op)} {t : List (Step A)} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = none →
      DialectDenote.denote (m := TraceM (Step A) (TraceState Mem unit)) o.op args s (.ok (rs, t, s₁)) →
      (o.results.map (·.1)).length = rs.toDVals.length →
      TCfg.Next M ⟨f, env, o :: os, s⟩ ⟨f, (o.results.map (·.1)).zip rs.toDVals ++ env, os, s₁⟩ t 1
  | ext {f : Func d} {env : Env d} {o : Operation d} {os : List (Operation d)}
      {s s₁ s₂ : TraceState Mem unit} {args : HVector toType (sig o.op)} {δ : Nat} {sym : Name}
      {ts : List d.Ty} {cargs : HVector toType ts} {t₀ : List (Step A)} {vs : List (DVal d)}
      {t : List (Step A)} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → Func.TCallsAt M o args s δ sym ts cargs 0 t₀ s₁ →
      M.func? sym = none → M.declares sym ts (returnTypes o.op) = true →
      DialectExtCall.extCall (m := TraceM (Step A) (TraceState Mem unit)) sym cargs.toDVals
        (returnTypes o.op) s₁ (.ok (vs, t, s₂)) →
      vs.map (·.1) = returnTypes o.op → (o.results.map (·.1)).length = vs.length →
      TCfg.Next M ⟨f, env, o :: os, s⟩ ⟨f, (o.results.map (·.1)).zip vs ++ env, os, s₂⟩ (t₀ ++ t)
        (δ + 1)
  | goto {f : Func d} {env env₁ : Env d} {o : Operation d} {os : List (Operation d)}
      {s s₁ : TraceState Mem unit} {args : HVector toType (sig o.op)} {i : Nat} {t : List (Step A)}
      {b : Block d} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = true → os = [] →
      DialectDenote.exit (m := TraceM (Step A) (TraceState Mem unit)) o.op args s (.ok (.goto i, t, s₁)) →
      f.jump env o.succs i = .ok (b, env₁) →
      TCfg.Next M ⟨f, env, o :: os, s⟩ ⟨f, env₁, b.body, s₁⟩ t 1
  | ret {f : Func d} {env : Env d} {o : Operation d} {os : List (Operation d)}
      {s s₁ s₂ : TraceState Mem unit} {args : HVector toType (sig o.op)} {δ : Nat} {sym : Name}
      {ts : List d.Ty} {cargs : HVector toType ts} {t₀ : List (Step A)} {g : Func d}
      {body : List (Operation d)} {genv : Env d} {U k : Nat} {vs : List (DVal d)}
      {t : List (Step A)} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → Func.TCallsAt M o args s δ sym ts cargs 0 t₀ s₁ →
      M.func? sym = some g → g.enter cargs.toDVals = .ok (body, genv) →
      Func.traceCall (Step A) M U g genv body s₁ (.ok (.ok (.ret (vs, k)), t, s₂)) →
      vs.map (·.1) = returnTypes o.op → (o.results.map (·.1)).length = vs.length →
      TCfg.Next M ⟨f, env, o :: os, s⟩ ⟨f, (o.results.map (·.1)).zip vs ++ env, os, s₂⟩ (t₀ ++ t)
        (U + δ + 1)

/-- A step of a frame is a move. -/
theorem TCfg.Next.move {c c₁ : TCfg d Mem unit} {t : List (Step A)} {F : Nat}
    (h : TCfg.Next A M c c₁ t F) : TCfg.Move A M c c₁ t F := by
  cases h with
  | denote hreg hargs hT hc hx hlen => exact .denote hreg hargs hT hc hx hlen
  | ext hreg hargs hT hc hg hd hx hty hlen => exact .ext hreg hargs hT hc hg hd hx hty hlen
  | goto hreg hargs hT hos hx hj => exact .goto hreg hargs hT hos hx hj
  | ret hreg hargs hT hc hg hen hx hty hlen => exact .ret hreg hargs hT hc hg hen hx hty hlen

section

variable [HRefinement A A] [TyRefinement d.Ty]

/-- A path of the configuration that a step of a frame goes on to, allowing
the target's path, gives one of the configuration, allowing the target's
path after acts that refine the step's: the step, then the path. -/
theorem TCfg.Next.tAllowed {c c₁ : TCfg d Mem unit} {t t' : List (Step A)} {F : Nat}
    (h : TCfg.Next A M c c₁ t F) (ht : Step.actsOf t ⊑ Step.actsOf t')
    {e' : TraceEnd (Step A) (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))}
    (ha : TAllowed (fun N => Func.traceOps (Step A) M N c₁.f c₁.env c₁.os c₁.s) e') :
    TAllowed (fun N => Func.traceOps (Step A) M N c.f c.env c.os c.s) (e'.after t') := by
  cases h with
  | denote hreg hargs hT hc hx hlen =>
    refine TAllowed.of_step (k := 0) (N₀ := 0) ht (fun N x hd hx₁ => ?_) ha
    rw [TraceEnd.addLeft_zero, Nat.zero_add]
    exact (Func.tStepPath_iff hd.notStuck.after).2 (.denote hreg hargs hT hc hx hlen hx₁)
  | goto hreg hargs hT hos hx hj =>
    refine TAllowed.of_step (k := 0) (N₀ := 0) ht (fun N x hd hx₁ => ?_) ha
    rw [TraceEnd.addLeft_zero, Nat.zero_add]
    exact (Func.tStepPath_iff hd.notStuck.after).2 (.goto hreg hargs hT hos hx hj hx₁)
  | @ext _ _ _ _ _ _ _ _ δ _ _ _ _ _ _ hreg hargs hT hc hg hd hx hty hlen =>
    refine TAllowed.of_step (k := 0) (N₀ := δ) ht (fun N x hdn hx₁ => ?_) ha
    rw [TraceEnd.addLeft_zero, ← TraceEnd.after_after, show δ + N + 1 = N + δ + 1 by omega]
    have hc' := hc.at N
    rw [Nat.sub_zero] at hc'
    exact (Func.tStepPath_iff hdn.notStuck.after.after).2 (.ext hreg hargs hT hc' hg hd hx hty hlen hx₁)
  | @ret _ _ _ _ _ _ _ _ δ _ _ _ _ _ _ _ U k _ _ hreg hargs hT hc hg hen hx hty hlen =>
    refine TAllowed.of_step (k := min k U) (N₀ := U + δ) ht (fun N x hdn hx₁ => ?_) ha
    have hcall := Func.traceCall_up N U hx trivial
    have hrest := Func.traceOps_up (min k U) N _ _ _ _ _ hx₁ hdn
    have hmin : min (k + N) (U + N) = N + min k U := by
      rw [Nat.add_min_add_right, Nat.add_comm]
    have hc' := hc.at (U + N)
    rw [Nat.sub_zero] at hc'
    rw [← TraceEnd.after_after, show U + δ + N + 1 = U + N + δ + 1 by omega]
    exact (Func.tStepPath_iff ((hdn.addLeft _).notStuck.after.after)).2
      (.callRet hreg hargs hT hc' hg hen hcall hty hlen (hmin ▸ hrest))

/-- The source's configuration `c` is matched with the target's `c'`: the same
ops of the same function, from an environment and a traced state that the
target's refine. -/
structure TCfg.Matched (c c' : TCfg d Mem unit) : Prop where
  f : c.f = c'.f
  os : c.os = c'.os
  env : c.env.IsRefinedBy c'.env
  s : c.s ⊑ c'.s

variable (A) in
/-- A guard of the source module `M` and the target module `M'`, under the
agreement `agree` of two external calls: a set `G` of pairs of
configurations, the source's first, closed in three ways. Where the target
goes on by a step of its frame, and the source has a step that ends matched
with it, with acts that the target's refine, the source has one that ends
in a pair of `G`. Where the target enters a callee that both modules run,
and the source calls it on arguments that the target's refine, the source
has such a call whose entry into the callee is paired with the target's in
`G`. Where the target calls an external declaration, and the source calls
it on arguments that the target's refine, the source has such a call where
the two agree. -/
structure TCfg.Guard
    (agree : List (DVal d) → TraceState Mem unit → List (DVal d) → TraceState Mem unit → Prop)
    (M M' : Module d) (G : TCfg d Mem unit → TCfg d Mem unit → Prop) : Prop where
  next : ∀ {c c' c₁' : TCfg d Mem unit} {t' : List (Step A)} {F' : Nat}, G c c' →
    TCfg.Next A M' c' c₁' t' F' →
    (∃ c₁ t F, TCfg.Next A M c c₁ t F ∧ c₁.Matched c₁' ∧ Step.actsOf t ⊑ Step.actsOf t') →
    ∃ c₁ t F, TCfg.Next A M c c₁ t F ∧ c₁.Matched c₁' ∧ Step.actsOf t ⊑ Step.actsOf t' ∧ G c₁ c₁'
  enter : ∀ {c c' : TCfg d Mem unit} {o : Operation d} {os : List (Operation d)}
    {args args' : HVector toType (sig o.op)} {n n' : Nat} {sym : Name} {ts : List d.Ty}
    {cargs' : HVector toType ts} {t₀' : List (Step A)} {s₁' : TraceState Mem unit} {g : Func d}
    {body : List (Operation d)} {genv' : Env d}, G c c' → c.os = o :: os → c'.os = o :: os →
    c.env.operands (sig o.op) o.operands = .ok args →
    c'.env.operands (sig o.op) o.operands = .ok args' → isTerminator o.op = false →
    Func.TCallsAt M' o args' c'.s n sym ts cargs' n' t₀' s₁' → M.func? sym = some g →
    M'.func? sym = some g → g.enter cargs'.toDVals = .ok (body, genv') →
    (∃ (cargs : HVector toType ts) (t₀ : List (Step A)) (s₁ : TraceState Mem unit),
      Func.TCallsAt M o args c.s n sym ts cargs n' t₀ s₁ ∧
      cargs.Forall₂ TyRefinement.IsRefinedBy cargs' ∧ t₀ ⊑ t₀' ∧ s₁ ⊑ s₁') →
    ∃ (cargs : HVector toType ts) (t₀ : List (Step A)) (s₁ : TraceState Mem unit) (genv : Env d),
      Func.TCallsAt M o args c.s n sym ts cargs n' t₀ s₁ ∧
      cargs.Forall₂ TyRefinement.IsRefinedBy cargs' ∧ t₀ ⊑ t₀' ∧ s₁ ⊑ s₁' ∧
      g.enter cargs.toDVals = .ok (body, genv) ∧
      G ⟨g, genv, body, { s₁ with mem := s₁.mem.enter }⟩
        ⟨g, genv', body, { s₁' with mem := s₁'.mem.enter }⟩
  ext : ∀ {c c' : TCfg d Mem unit} {o : Operation d} {os : List (Operation d)}
    {args args' : HVector toType (sig o.op)} {n n' : Nat} {sym : Name} {ts : List d.Ty}
    {cargs' : HVector toType ts} {t₀' : List (Step A)} {s₁' : TraceState Mem unit}, G c c' →
    c.os = o :: os → c'.os = o :: os → c.env.operands (sig o.op) o.operands = .ok args →
    c'.env.operands (sig o.op) o.operands = .ok args' → isTerminator o.op = false →
    Func.TCallsAt M' o args' c'.s n sym ts cargs' n' t₀' s₁' → M'.func? sym = none →
    (∃ (cargs : HVector toType ts) (t₀ : List (Step A)) (s₁ : TraceState Mem unit),
      Func.TCallsAt M o args c.s n sym ts cargs n' t₀ s₁ ∧
      cargs.Forall₂ TyRefinement.IsRefinedBy cargs' ∧ t₀ ⊑ t₀' ∧ s₁ ⊑ s₁') →
    ∃ (cargs : HVector toType ts) (t₀ : List (Step A)) (s₁ : TraceState Mem unit),
      Func.TCallsAt M o args c.s n sym ts cargs n' t₀ s₁ ∧
      cargs.Forall₂ TyRefinement.IsRefinedBy cargs' ∧ t₀ ⊑ t₀' ∧ s₁ ⊑ s₁' ∧
      agree cargs.toDVals s₁ cargs'.toDVals s₁'

/-- Where two external calls always agree, the set of all pairs of
configurations is a guard: each clause gives back the source's step that
it is handed. -/
theorem TCfg.Guard.always {M M' : Module d} :
    TCfg.Guard A ExtAgree.always M M' fun (_ _ : TCfg d Mem unit) => True where
  next := fun _ _ ⟨c₁, t, F, hn, hm, ht⟩ => ⟨c₁, t, F, hn, hm, ht, trivial⟩
  enter := fun _ _ _ _ _ _ _ _ _ hen' ⟨cargs, t₀, s₁, hc, hr, ht, hs⟩ => by
    obtain ⟨genv, hen, -⟩ := Func.enter_isRefinedBy (HVector.toDVals_isRefinedBy hr) hen'
    exact ⟨cargs, t₀, s₁, genv, hc, hr, ht, hs, hen, trivial⟩
  ext := fun _ _ _ _ _ _ _ _ ⟨cargs, t₀, s₁, hc, hr, ht, hs⟩ =>
    ⟨cargs, t₀, s₁, hc, hr, ht, hs, trivial⟩

omit [DecidableEq Mem] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (TraceM (Step A) (TraceState Mem unit))]
  [DialectExtCall d (TraceM (Step A) (TraceState Mem unit))] [HRefinement A A] in
/-- An environment refines itself when every value does. -/
theorem Env.isRefinedBy_refl (hrefl : ∀ {t : d.Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v) :
    ∀ env : Env d, env.IsRefinedBy env
  | [] => trivial
  | _ :: env => ⟨rfl, ⟨rfl, hrefl _⟩, Env.isRefinedBy_refl hrefl env⟩

omit [DecidableEq Mem] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (TraceM (Step A) (TraceState Mem unit))]
  [DialectExtCall d (TraceM (Step A) (TraceState Mem unit))] [TyRefinement d.Ty] in
/-- A marked trace refines itself when every act does. -/
theorem Step.list_isRefinedBy_refl (hA : ∀ a : A, a ⊑ a) (l : List (Step A)) : l ⊑ l :=
  List.isRefinedBy_refl (fun | .tick => trivial | .act a => hA a) l

/-- In one module, the pairs of equal configurations form a guard, under an
agreement that every call has with itself, when the refinement of values and
of acts is reflexive: the source takes the target's own step. -/
theorem TCfg.Guard.eq
    {agree : List (DVal d) → TraceState Mem unit → List (DVal d) → TraceState Mem unit → Prop}
    (hag : ∀ vs s, agree vs s vs s)
    (hrefl : ∀ {t : d.Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v) (hA : ∀ a : A, a ⊑ a) :
    TCfg.Guard A agree M M fun c c' => c = c' where
  next := fun {c c' c₁' t' F'} hG hn _ => by
    subst hG
    exact ⟨c₁', t', F', hn, ⟨rfl, rfl, Env.isRefinedBy_refl hrefl _, TraceState.isRefinedBy_refl _⟩,
      List.isRefinedBy_refl (fun a => hA a) _, rfl⟩
  enter := fun {c c' o os args args' n n' sym ts cargs' t₀' s₁' g body genv'} hG _ _ hargs hargs' _
      hc _ _ hen' _ => by
    subst hG
    rw [hargs] at hargs'
    cases hargs'
    exact ⟨cargs', t₀', s₁', genv', hc, HVector.forall₂_refl (fun v => hrefl v) _,
      Step.list_isRefinedBy_refl hA _, TraceState.isRefinedBy_refl _, hen', rfl⟩
  ext := fun {c c' o os args args' n n' sym ts cargs' t₀' s₁'} hG _ _ hargs hargs' _ hc _ _ => by
    subst hG
    rw [hargs] at hargs'
    cases hargs'
    exact ⟨cargs', t₀', s₁', hc, HVector.forall₂_refl (fun v => hrefl v) _,
      Step.list_isRefinedBy_refl hA _, TraceState.isRefinedBy_refl _, hag _ _⟩

variable {agree : List (DVal d) → TraceState Mem unit → List (DVal d) → TraceState Mem unit → Prop}
  {G : TCfg d Mem unit → TCfg d Mem unit → Prop}

/-- A return or UB of a call's callee in the target, in its frame, is
allowed by the source's callee in its frame: the same function, by the
induction `ih`, from the callee's entry paired in the guard `G`, or a black
box. The induction is asked only of a function of the source module, whose
ops are monotone, from the ops of its entry block. -/
theorem TraceCallsRefined.callee_allowed {M M' : Module d}
    (hc : TraceCallsRefined A Mem unit M M')
    (hmono : ∀ g ∈ M.funcs, g.TraceOpsMonotone (Step A) (TraceState Mem unit) agree)
    {sym : Name} {g₀ : Func d} (hg' : M'.func? sym = some g₀) {ts : List d.Ty}
    {args args' : HVector toType ts} (hr : args.Forall₂ TyRefinement.IsRefinedBy args')
    {s s' : TraceState Mem unit} (hs : s ⊑ s') {p' : List (Operation d) × Env d}
    (hen' : g₀.enter args'.toDVals = .ok p')
    (hG : M'.func? sym = M.func? sym → ∀ genv, g₀.enter args.toDVals = .ok (p'.1, genv) →
      G ⟨g₀, genv, p'.1, { s with mem := s.mem.enter }⟩ ⟨g₀, p'.2, p'.1, { s' with mem := s'.mem.enter }⟩)
    {n : Nat}
    (ih : g₀.TraceOpsMonotone (Step A) (TraceState Mem unit) agree →
      TraceMonotoneOps (Step A) (TraceState Mem unit) p'.1 agree → ∀ (env env' : Env d),
      env.IsRefinedBy env' → ∀ (t t' : TraceState Mem unit), t ⊑ t' →
      G ⟨g₀, env, p'.1, t⟩ ⟨g₀, env', p'.1, t'⟩ →
      ∀ e', Func.traceOps (Step A) M' n g₀ env' p'.1 t' e' →
        TAllowed (fun N => Func.traceOps (Step A) M N g₀ env p'.1 t) e')
    {e' : TraceEnd (Step A) (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))}
    (he' : Func.traceCall (Step A) M' n g₀ p'.2 p'.1 s' e') (hd : e'.Done) :
    ∃ g p, M.func? sym = some g ∧ g.enter args.toDVals = .ok p ∧
      TAllowed (fun N => Func.traceCall (Step A) M N g p.2 p.1 s) e' := by
  rcases hc.1 sym with hsame | ⟨g, g', hg, hg'', bb⟩
  · obtain ⟨genv, hen, hgenv⟩ := Func.enter_isRefinedBy (HVector.toDVals_isRefinedBy hr) hen'
    have hg : M.func? sym = some g₀ := hsame ▸ hg'
    have hf := hmono g₀ (List.mem_of_find?_eq_some hg)
    exact ⟨g₀, (p'.1, genv), hg, hen, Func.traceCall_tAllowed
      (fun e₀ he₀ => ih hf (hf.enter hen') genv p'.2 hgenv _ _ (TraceState.IsRefinedBy.enter hs)
        (hG hsame genv hen) e₀ he₀) he'⟩
  · rw [hg''] at hg'
    cases hg'
    obtain ⟨p, hen, hm⟩ := bb.allowed hr hs hen' he' hd
    exact ⟨g, p, hg, hen, hm⟩

end

end Fir
