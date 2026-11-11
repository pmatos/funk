import Fir.Execution.MemoryRefineUp

/-!
# Divergence of the target with memory, allowed

A target that diverges runs out of fuel at every budget, and the source
must then diverge too, or hit UB at some budget. The proof is the proof for
runs in the set monad (the section on divergence of the target, allowed),
read from given memories. Let _B_ be the black box's bound plus one, and
let the target's budget be at least _B_ times one more than the source's.
Then a path of the target's run of ops that runs out of fuel or returns is
allowed by the source at its budget: the source runs out of fuel there, or
hits UB at some budget, or, on a return, returns there what refines to the
target's, with memories that the target's refine, while the target leaves
at least _B_ times the steps that the source leaves, plus _B_.

The proof is by strong induction on the target's budget, from every
memories. Each op takes one step in both runs, a call of the same function
included, whose callee the induction covers from the memories with a frame
entered. A black-box call is where the budgets part, as in the set monad:
its target diverges from the call's arguments and memories, so its source
diverges or hits UB there; or it returns within the bound, and its source,
whose runs are fuel-monotone, runs out of fuel at its budget or returns
there what the black box allows.
-/

namespace Fir

open SetM Memory

section

variable {α : Type} [HRefinement α α]

/-- The source `src` at the budget `N` allows the target's path that runs
out of fuel or returns: it runs out of fuel at `N`, or hits UB at some
budget, or, on a return, it returns at `N` what refines to the target's, and
leaves at most a `B`th of the steps that the target leaves. A path that
hits UB or is stuck asks nothing here. -/
def MemAllowedBelow (B : Nat) (src : Nat → ExceptT Stuck SetM (Result (α × Nat))) (N : Nat) :
    Ev (Except Stuck (Result (α × Nat))) → Prop
  | .ok (.ok .fuelExhausted) => (src N).run (.ok (.ok .fuelExhausted)) ∨ SomeUB src
  | .ok (.ok (.ret (a', k'))) => (src N).run (.ok (.ok .fuelExhausted)) ∨ SomeUB src ∨
    ∃ a k, (src N).run (.ok (.ok (.ret (a, k)))) ∧ a ⊑ a' ∧ B * (k + 1) ≤ k'
  | _ => True

variable {B N : Nat} {src c : Nat → ExceptT Stuck SetM (Result (α × Nat))}
  {e : Ev (Except Stuck (Result (α × Nat)))}

/-- UB at some budget allows every path. -/
theorem MemAllowedBelow.of_someUB (h : SomeUB src) : ∀ e, MemAllowedBelow B src N e
  | .ok (.ok .fuelExhausted) => .inr h
  | .ok (.ok (.ret _)) => .inr (.inl h)
  | .ub _ | .ok (.error _) => trivial

/-- Running out of fuel at `N` allows every path. -/
theorem MemAllowedBelow.of_exhausted (h : (src N).run (.ok (.ok .fuelExhausted))) :
    ∀ e, MemAllowedBelow B src N e
  | .ok (.ok .fuelExhausted) => .inl h
  | .ok (.ok (.ret _)) => .inl h
  | .ub _ | .ok (.error _) => trivial

/-- A path that hits UB or is stuck is allowed by every source. -/
theorem MemAllowedBelow.of_not (h : ¬ (Ev.NotStuck e ∧ ∀ r, e ≠ .ub r)) :
    MemAllowedBelow B src N e := by
  match e with
  | .ub _ | .ok (.error _) => trivial
  | .ok (.ok .fuelExhausted) | .ok (.ok (.ret _)) =>
    exact (h ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩).elim

/-- A path allowed by the rest of a run at the budget `N` is allowed by the
whole at `N'`, when every way that the rest ends at `N` is a way that the
whole ends at `N'`, and UB of the rest at some budget is UB of the whole at
some budget. -/
theorem MemAllowedBelow.of_step {N' : Nat}
    (hstep : ∀ x, Ev.NotStuck x → (c N).run x → (src N').run x)
    (hub : SomeUB c → SomeUB src) : MemAllowedBelow B c N e → MemAllowedBelow B src N' e := by
  match e with
  | .ub _ | .ok (.error _) => exact fun _ => trivial
  | .ok (.ok .fuelExhausted) =>
    rintro (h | h)
    · exact .inl (hstep _ (fun _ h => nomatch h) h)
    · exact .inr (hub h)
  | .ok (.ok (.ret _)) =>
    rintro (h | h | ⟨a, k, h, hr, hk⟩)
    · exact .inl (hstep _ (fun _ h => nomatch h) h)
    · exact .inr (.inl (hub h))
    · exact .inr (.inr ⟨a, k, hstep (.ok (.ok (.ret (a, k)))) (fun _ h => nomatch h) h, hr, hk⟩)

end

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (StateT (Memories Mem unit) SetM)] [TyRefinement d.Ty]

/-- A path of a callee in the target's frame that runs out of fuel or
returns is allowed at `N₀` by the source's callee in its frame, when each
such path of the target's callee's ops, from the memories with a frame
entered, is allowed by the source's: leaving a frame keeps refinement. -/
theorem Func.memCall_allowedBelow {M M' : Module d} {n B N₀ : Nat} {g g' : Func d}
    {genv genv' : Env d} {body body' : List (Operation d)} {S S' : Memories Mem unit}
    (h : ∀ e₀, (Func.memOps M' n g' genv' body' S'.enter).run e₀ →
      MemAllowedBelow B (fun N => Func.memOps M N g genv body S.enter) N₀ e₀)
    {e' : Ev (Except Stuck (Result ((List (DVal d) × Memories Mem unit) × Nat)))}
    (he' : (Func.memCall M' n g' genv' body' S').run e') :
    MemAllowedBelow B (fun N => Func.memCall M N g genv body S) N₀ e' := by
  have map : ∀ {N x}, (Func.memOps M N g genv body S.enter).run (.ok (.ok x)) →
      (Func.memCall M N g genv body S).run (.ok (.ok (Result.mapVal
        (fun p : List (DVal d) × Memories Mem unit => (p.1, p.2.exit)) x))) := fun hx => by
    rw [Func.memCall_eq]
    exact (SetM.run_map _ _ _).2 (.inl ⟨_, hx, rfl⟩)
  have ub : SomeUB (fun N => Func.memOps M N g genv body S.enter) →
      SomeUB (fun N => Func.memCall M N g genv body S) := fun ⟨N, r, h⟩ =>
    ⟨N, r, by
      show (Func.memCall M N g genv body S).run _
      rw [Func.memCall_eq]
      exact (SetM.run_map _ _ _).2 (.inr (.inr ⟨r, h, rfl⟩))⟩
  rw [Func.memCall_eq] at he'
  rcases (SetM.run_map _ _ _).1 he' with ⟨r, hr, rfl⟩ | ⟨_, _, rfl⟩ | ⟨r, hr, rfl⟩
  · match r, hr with
    | .fuelExhausted, hr =>
      rcases h _ hr with hx | hu
      · exact .inl (map hx)
      · exact .inr (ub hu)
    | .ret ((vs', T'), k'), hr =>
      rcases h _ hr with hx | hu | ⟨⟨vs, T⟩, k, hx, hle, hk⟩
      · exact .inl (map hx)
      · exact .inr (.inl (ub hu))
      · exact .inr (.inr ⟨(vs, T.exit), k, map hx, ⟨hle.1, hle.2.exit⟩, hk⟩)
  · trivial
  · trivial

/-- A path of a black box's target in its frame that runs out of fuel or
returns, called on arguments and from memories that refine the source's,
at a budget `n` of at least `bound + (bound + 1) * (N₀ + 1)`, is allowed by
the source's callee in its frame at `N₀`, which starts. -/
theorem MemBlackBox.allowedBelow {M M' : Module d} {bound : Nat} {g g' : Func d}
    (bb : MemBlackBox (Mem := Mem) (unit := unit) M M' bound g g') {ts : List d.Ty}
    {args args' : HVector toType ts} (hr : args.Forall₂ TyRefinement.IsRefinedBy args')
    {S S' : Memories Mem unit} (hS : S ⊑ S') {n N₀ : Nat}
    (hn : bound + (bound + 1) * (N₀ + 1) ≤ n) {p' : List (Operation d) × Env d}
    (hen' : g'.enter args'.toDVals = .ok p')
    {e' : Ev (Except Stuck (Result ((List (DVal d) × Memories Mem unit) × Nat)))}
    (he' : (Func.memCall M' n g' p'.2 p'.1 S').run e')
    (hne : Ev.NotStuck e') (hub : ∀ r, e' ≠ .ub r) :
    ∃ p, g.enter args.toDVals = .ok p ∧
      MemAllowedBelow (bound + 1) (fun N => Func.memCall M N g p.2 p.1 S) N₀ e' := by
  have hsig := bb.sig hen'
  have hrun := fun {m x} => bb.target_run hen' (S' := S') (m := m) (x := x)
  have href := bb.refines _ _ S S' (HVector.forall₂_cast hsig hr) hS
  have inv := fun {N x} => Func.memRunsFrom_run_cast (M := M) (args := args) (S := S) (N := N) (x := x) hsig
  have ofUB : ∀ {N : Nat} {r : String}, (g.memRunsFrom M (args.cast hsig, S) N).outcomes (.ub r) →
      ∃ p, g.enter args.toDVals = .ok p ∧
        MemAllowedBelow (bound + 1) (fun N => Func.memCall M N g p.2 p.1 S) N₀ e' := by
    intro N r h
    obtain ⟨p, hp, e, he, hx⟩ := inv (x := .ub r) (fun _ h => nomatch h) h
    match e, he, hx with
    | .ub _, he, rfl => exact ⟨p, hp, MemAllowedBelow.of_someUB ⟨N, r, he⟩ _⟩
  have ofExh : (g.memRunsFrom M (args.cast hsig, S) N₀).outcomes .fuelExhausted →
      ∃ p, g.enter args.toDVals = .ok p ∧
        MemAllowedBelow (bound + 1) (fun N => Func.memCall M N g p.2 p.1 S) N₀ e' := by
    intro h
    obtain ⟨p, hp, e, he, hx⟩ := inv (x := .ok (.ok .fuelExhausted)) (fun _ h => nomatch h) h
    match e, he, hx with
    | .ok (.ok .fuelExhausted), he, _ => exact ⟨p, hp, MemAllowedBelow.of_exhausted he _⟩
  rcases bb.bounded ((args'.cast hsig).cast bb.params.symm, S') with hdiv | hbdd
  · obtain ⟨s₀, hs₀, hle⟩ := href .fuelExhausted hdiv
    match s₀, hs₀, hle with
    | .ub r, ⟨N, hN⟩, _ => exact ofUB hN
    | .fuelExhausted, hs₀, _ => exact ofExh (hs₀ N₀)
    | .ret _, _, hle => exact hle.elim
  have hbn : bound ≤ n := by omega
  match e', he', hne, hub with
  | .ok (.ok .fuelExhausted), he', hne, _ => exact absurd (hrun hne he') (hbdd n hbn)
  | .ok (.ok (.ret (vs', k'))), he', hne, _ =>
    have hk' : n - bound ≤ k' := by
      have ha := Func.memCall_ahead M' bound (n - bound) g' p'.2 p'.1 S'
      rw [Nat.add_sub_cancel' hbn] at ha
      rcases ha.down_ret _ _ he' with ⟨h, _⟩ | h
      · exact h
      · exact absurd (hrun (x := .ok (.ok .fuelExhausted)) (fun _ h => nomatch h) h)
          (hbdd bound (Nat.le_refl _))
    obtain ⟨s₀, hs₀, hle⟩ := href (.ret vs') ⟨n, hrun hne he'⟩
    match s₀, hs₀, hle with
    | .ub r, ⟨N, hN⟩, _ => exact ofUB hN
    | .fuelExhausted, _, hle => exact hle.elim
    | .ret vs, ⟨N₁, hN₁⟩, hvs =>
      classical
      by_cases hex : (g.memRunsFrom M (args.cast hsig, S) N₀).outcomes .fuelExhausted
      · exact ofExh hex
      have hfm := Func.memRunsFrom_fuelMonotone M g (args.cast hsig) S
      have hret : (g.memRunsFrom M (args.cast hsig, S) N₀).outcomes (.ret vs) := by
        rcases Nat.le_total N₁ N₀ with h | h
        · exact hfm.up (o := .ret vs) h (fun h => nomatch h) hN₁
        · exact (hfm.down (o := .ret vs) h (fun h => nomatch h) hN₁).resolve_right hex
      obtain ⟨p, hp, e, he, hx⟩ := inv (x := .ok (.ok (.ret vs))) (fun _ h => nomatch h) hret
      match e, he, hx with
      | .ok (.ok (.ret (_, k))), he, rfl =>
        have hk := Func.memCall_left_le M N₀ g p.2 p.1 S _ _ he
        have hmul : (bound + 1) * (k + 1) ≤ (bound + 1) * (N₀ + 1) :=
          Nat.mul_le_mul_left _ (Nat.succ_le_succ hk)
        exact ⟨p, hp, .inr (.inr ⟨vs, k, he, hvs, by omega⟩)⟩
  | .ub r, _, _, hub => exact absurd rfl (hub r)
  | .ok (.error st), _, hne, _ => exact absurd rfl (hne st)

/-- A path of a call's callee in the target, in its frame, that runs out of
fuel or returns is allowed at `N₀` by the source's callee in its frame: the
same function, by the induction `ih`, or a black box. -/
theorem MemCallsRefined.callee_allowedBelow {M M' : Module d} {bound : Nat}
    (hc : MemCallsRefined Mem unit M M' bound) (hmono : ∀ g ∈ M.funcs, g.MemOpsMonotone Mem unit)
    {s : Name} {g₀ : Func d} (hg' : M'.func? s = some g₀) {ts : List d.Ty}
    {args args' : HVector toType ts} (hr : args.Forall₂ TyRefinement.IsRefinedBy args')
    {S S' : Memories Mem unit} (hS : S ⊑ S') {p' : List (Operation d) × Env d}
    (hen' : g₀.enter args'.toDVals = .ok p') {n N₀ : Nat}
    (hn : bound + (bound + 1) * (N₀ + 1) ≤ n)
    (ih : g₀.MemOpsMonotone Mem unit → MemMonotoneOps Mem unit p'.1 → ∀ (env env' : Env d),
      env.IsRefinedBy env' → ∀ (T T' : Memories Mem unit), T ⊑ T' →
      ∀ e', (Func.memOps M' n g₀ env' p'.1 T').run e' →
        MemAllowedBelow (bound + 1) (fun N => Func.memOps M N g₀ env p'.1 T) N₀ e')
    {e' : Ev (Except Stuck (Result ((List (DVal d) × Memories Mem unit) × Nat)))}
    (he' : (Func.memCall M' n g₀ p'.2 p'.1 S').run e')
    (hne : Ev.NotStuck e') (hub : ∀ r, e' ≠ .ub r) :
    ∃ g p, M.func? s = some g ∧ g.enter args.toDVals = .ok p ∧
      MemAllowedBelow (bound + 1) (fun N => Func.memCall M N g p.2 p.1 S) N₀ e' := by
  rcases hc s with hsame | ⟨g, g', hg, hg'', bb⟩
  · obtain ⟨genv, hen, hgenv⟩ := Func.enter_isRefinedBy (HVector.toDVals_isRefinedBy hr) hen'
    have hg : M.func? s = some g₀ := hsame ▸ hg'
    have hf := hmono g₀ (List.mem_of_find?_eq_some hg)
    exact ⟨g₀, (p'.1, genv), hg, hen, Func.memCall_allowedBelow
      (fun e₀ he₀ => ih hf (hf.enter hen') genv p'.2 hgenv _ _ hS.enter e₀ he₀) he'⟩
  · rw [hg''] at hg'
    cases hg'
    obtain ⟨p, hen, hm⟩ := bb.allowedBelow hr hS hn hen' he' hne hub
    exact ⟨g, p, hg, hen, hm⟩

end Fir
