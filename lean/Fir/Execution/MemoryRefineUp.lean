import Fir.Execution.MemoryBlackBox
import Fir.Execution.MemoryOpRefine

/-!
# Every return and UB of the target with memory, allowed

Let every call name the same function in both modules or a black box with
memory. Let every op that runs by its own rule, a terminator or an op with
no callee, be monotone with memory, among the ops of the source module's
functions and of the function that runs. Then every return and every UB of
the target's run of ops, from an environment that refines the source's and
from memories that refine the source's, is allowed by the source's run of
the same ops at some budget. Calls and recursion are included.

The proof is the proof for runs in the set monad (the section on every
return and UB of the target, allowed), read from given memories, by strong
induction on the target's budget, for every function at once and from every
memories:

* An op's operands are found in the source's environment too, refined, and
  it starts from memories that the target's refine. What it does is allowed
  by what it does in the source: UB there allows anything; otherwise the
  source gives results that the target's refine, or goes to the same place,
  with memories that the target's refine. The induction covers the rest.
* A call of the same function in both enters it at the same op, in
  environments of which the target's refines the source's, from memories
  with a frame entered, of which the target's refine the source's too; the
  induction covers the callee. Leaving a frame keeps refinement, so the
  callee's return in its frame is allowed by the source's. A call of a black
  box is allowed by the black box's behaviours, which speak of the memories
  the call starts and ends with.
* When the source's callee returns at one budget, and the rest of the
  source's run is allowed at another, the source's run is allowed at their
  sum plus one, as in the set monad.
-/

namespace Fir

open SetM Memory

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (StateT (Memories Mem unit) SetM)] [TyRefinement d.Ty]

omit [DecidableEq Mem] [DecidableEq d.Ty] [DialectCall d] in
variable (Mem unit) in
/-- Every op of `os` that runs by its own rule, a terminator or an op with
no callee, is monotone with memory. -/
def MemMonotoneOps (os : List (Operation d)) : Prop :=
  ∀ o ∈ os, isTerminator o.op = true ∨ callee? o.op = none →
    OpMemMonotone (σ := Memories Mem unit) o.op

omit [DecidableEq Mem] [DecidableEq d.Ty] in
variable (Mem unit) in
/-- Every op of the function `f` that runs by its own rule is monotone with
memory. -/
def Func.MemOpsMonotone (f : Func d) : Prop :=
  ∀ b ∈ f.blocks, MemMonotoneOps Mem unit b.body

/-- A run of `f` starts at the ops of one of its blocks. -/
theorem Func.MemOpsMonotone.enter {f : Func d} (hf : f.MemOpsMonotone Mem unit)
    {dvs : List (DVal d)} {p : List (Operation d) × Env d} (hen : f.enter dvs = .ok p) :
    MemMonotoneOps Mem unit p.1 := by
  obtain ⟨e, he, -, -, rfl⟩ := Func.enter_eq_ok hen
  exact hf e (List.mem_of_mem_head? he)

/-- A jump of `f` goes to the ops of one of its blocks. -/
theorem Func.MemOpsMonotone.jump {f : Func d} (hf : f.MemOpsMonotone Mem unit) {env : Env d}
    {succs : List Succ} {i : Nat} {b : Block d} {env₁ : Env d}
    (hj : f.jump env succs i = .ok (b, env₁)) : MemMonotoneOps Mem unit b.body := by
  obtain ⟨s, vs, -, hb, -⟩ := Func.jump_eq_ok hj
  exact hf b (Func.block?_some hb).1

/-- A return or UB of a call's callee in the target, in its frame, is
allowed by the source's callee in its frame: the same function, by the
induction `ih`, or a black box. The induction is asked only of a function
of the source module, whose ops are monotone with memory, from the ops of
its entry block. -/
theorem MemCallsRefined.callee_allowed {M M' : Module d} {bound : Nat}
    (hc : MemCallsRefined Mem unit M M' bound) (hmono : ∀ g ∈ M.funcs, g.MemOpsMonotone Mem unit)
    {s : Name} {g₀ : Func d} (hg' : M'.func? s = some g₀) {ts : List d.Ty}
    {args args' : HVector toType ts} (hr : args.Forall₂ TyRefinement.IsRefinedBy args')
    {S S' : Memories Mem unit} (hS : S ⊑ S') {p' : List (Operation d) × Env d}
    (hen' : g₀.enter args'.toDVals = .ok p') {n : Nat}
    (ih : g₀.MemOpsMonotone Mem unit → MemMonotoneOps Mem unit p'.1 → ∀ (env env' : Env d),
      env.IsRefinedBy env' → ∀ (T T' : Memories Mem unit), T ⊑ T' →
      ∀ e', (Func.memOps M' n g₀ env' p'.1 T').run e' →
        MemAllowed (fun N => Func.memOps M N g₀ env p'.1 T) e')
    {e' : Ev (Except Stuck (Result ((List (DVal d) × Memories Mem unit) × Nat)))}
    (he' : (Func.memCall M' n g₀ p'.2 p'.1 S').run e')
    (hne : Ev.NotStuck e') (hexh : e' ≠ .ok (.ok .fuelExhausted)) :
    ∃ g p, M.func? s = some g ∧ g.enter args.toDVals = .ok p ∧
      MemAllowed (fun N => Func.memCall M N g p.2 p.1 S) e' := by
  rcases hc s with hsame | ⟨g, g', hg, hg'', bb⟩
  · obtain ⟨genv, hen, hgenv⟩ := Func.enter_isRefinedBy (HVector.toDVals_isRefinedBy hr) hen'
    have hg : M.func? s = some g₀ := hsame ▸ hg'
    have hf := hmono g₀ (List.mem_of_find?_eq_some hg)
    exact ⟨g₀, (p'.1, genv), hg, hen, Func.memCall_allowed
      (fun e₀ he₀ => ih hf (hf.enter hen') genv p'.2 hgenv _ _ hS.enter e₀ he₀) he'⟩
  · rw [hg''] at hg'
    cases hg'
    obtain ⟨p, hen, hm⟩ := bb.allowed hr hS hen' he' hne hexh
    exact ⟨g, p, hg, hen, hm⟩

/-- Every return and UB of the target's run of ops with memory is allowed
by the source's at some budget, from environments and memories of which the
target's refine the source's, when every call names the same function in
both modules or a black box, and every terminator and every op with no
callee is monotone with memory, among the ops of the source module's
functions, of the function `f` that runs, and of the ops `os` it runs. -/
theorem Func.memOps_allowed {M M' : Module d} (hmono : ∀ g ∈ M.funcs, g.MemOpsMonotone Mem unit)
    {bound : Nat} (hcalls : MemCallsRefined Mem unit M M' bound) (n : Nat) :
    ∀ (f : Func d) (env env' : Env d) (os : List (Operation d)) (S S' : Memories Mem unit),
      f.MemOpsMonotone Mem unit → MemMonotoneOps Mem unit os → env.IsRefinedBy env' → S ⊑ S' →
      ∀ e', (Func.memOps M' n f env' os S').run e' →
        MemAllowed (fun N => Func.memOps M N f env os S) e' := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f env env' os S S' hf hops henv hS e' he'
    classical
    by_cases hgood : Ev.NotStuck e' ∧ e' ≠ .ok (.ok .fuelExhausted)
    case neg => exact MemAllowed.of_not hgood
    obtain ⟨hne, hexh⟩ := hgood
    have hub : ∀ {N : Nat} {r : String} {o : Operation d} {os : List (Operation d)},
        Func.MemStepPath M N f env o os S (.ub r) →
        (Func.memOps M (N + 1) f env (o :: os) S).run (.ub r) :=
      fun {_ r _ _} h => (Func.memStepPath_iff (e := .ub r) (fun _ h => nomatch h)).2 h
    match n, os, hops, he' with
    | 0, _, _, he' => exact absurd (Func.run_memOps_zero.1 he') hexh
    | n + 1, [], _, he' => exact absurd he' (Func.run_memOps_nil hne)
    | n + 1, o :: os, hops, he' =>
      have ihn := ih n (Nat.lt_succ_self n)
      have hmo := hops o List.mem_cons_self
      have hops' : MemMonotoneOps Mem unit os := fun o' h => hops o' (List.mem_cons_of_mem _ h)
      have step : ∀ {c : Nat → ExceptT Stuck SetM
            (Result ((List (DVal d) × Memories Mem unit) × Nat))},
          (∀ N x, Ev.NotStuck x → (c N).run x → Func.MemStepPath M N f env o os S x) →
          MemAllowed c e' → MemAllowed (fun N => Func.memOps M N f env (o :: os) S) e' :=
        fun hcp => MemAllowed.of_step (k := 0) 0 fun N x hx _ h => by
          rw [Nat.zero_add]
          match x, hx, h with
          | .ok (.ok (.ret (a, i))), hx, h => exact (Func.memStepPath_iff hx).2 (hcp N _ hx h)
          | .ub r, hx, h => exact (Func.memStepPath_iff hx).2 (hcp N _ hx h)
          | .ok (.ok .fuelExhausted), hx, h => exact (Func.memStepPath_iff hx).2 (hcp N _ hx h)
          | .ok (.error st), hx, _ => exact absurd rfl (hx st)
      cases (Func.memStepPath_iff hne).1 he' with
      | exitUB hreg hargs' hT hos hx =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmo (.inl hT) args _ hr).2 hT S S' hS _ hx
        match e₀, he₀, hle with
        | .ub r, he₀, _ => exact MemAllowed.of_someUB ⟨1, r, hub (.exitUB hreg hargs hT hos he₀)⟩ _
      | ret hreg hargs' hT hos hx hs =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmo (.inl hT) args _ hr).2 hT S S' hS _ hx
        match e₀, he₀, hle with
        | .ub r, he₀, _ => exact MemAllowed.of_someUB ⟨1, r, hub (.exitUB hreg hargs hT hos he₀)⟩ _
        | .ok (_, S₁), he₀, ⟨rfl, hS₁⟩ =>
          exact .inr ⟨1, _, 0, (Func.memStepPath_iff (e := .ok (.ok (.ret ((args.toDVals, S₁), 0))))
            (fun _ h => nomatch h)).2 (.ret hreg hargs hT hos he₀ hs),
            HVector.toDVals_isRefinedBy hr, hS₁⟩
      | goto hreg hargs' hT hos hx hj he =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmo (.inl hT) args _ hr).2 hT S S' hS _ hx
        match e₀, he₀, hle with
        | .ub r, he₀, _ => exact MemAllowed.of_someUB ⟨1, r, hub (.exitUB hreg hargs hT hos he₀)⟩ _
        | .ok (_, S₁), he₀, ⟨rfl, hS₁⟩ =>
          obtain ⟨env₁, hj₁, henv₁⟩ := henv.jump hj
          exact step (fun N x _ h => .goto hreg hargs hT hos he₀ hj₁ h)
            (ihn _ _ _ _ _ _ hf (hf.jump hj) henv₁ hS₁ _ he)
      | denoteUB hreg hargs' hT hc hx =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmo (.inr hc) args _ hr).1 hT S S' hS _ hx
        match e₀, he₀, hle with
        | .ub r, he₀, _ =>
          exact MemAllowed.of_someUB ⟨1, r, hub (.denoteUB hreg hargs hT hc he₀)⟩ _
      | denote hreg hargs' hT hc hx hlen' he =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨e₀, he₀, hle⟩ := (hmo (.inr hc) args _ hr).1 hT S S' hS _ hx
        match e₀, he₀, hle with
        | .ub r, he₀, _ =>
          exact MemAllowed.of_someUB ⟨1, r, hub (.denoteUB hreg hargs hT hc he₀)⟩ _
        | .ok (rs, S₁), he₀, ⟨hrs, hS₁⟩ =>
          have hvs := HVector.toDVals_isRefinedBy hrs
          have hlen := hlen'.trans (DVals.length_eq_of_isRefinedBy hvs).symm
          exact step (fun N x _ h => .denote hreg hargs hT hc he₀ hlen h)
            (ihn _ _ _ _ _ _ hf hops' (henv.zip_append _ hvs) hS₁ _ he)
      | callUB hreg hargs' hT hc hg' hen' hx =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨g, p, hg, hen, hm⟩ := hcalls.callee_allowed hmono hg' hr hS (p' := (_, _)) hen'
          (fun hgm hbm env env' h T T' hT e' he' => ihn _ env env' _ T T' hgm hbm h hT e' he') hx
          (fun _ h => nomatch h) (fun h => nomatch h)
        obtain ⟨N, r, hN⟩ := hm
        exact MemAllowed.of_someUB ⟨N + 1, r, hub (.callUB hreg hargs hT hc hg hen hN)⟩ _
      | callExh _ _ _ _ _ _ _ => exact absurd rfl hexh
      | callRet hreg hargs' hT hc hg' hen' hx hty' hlen' he =>
        obtain ⟨args, hargs, hr⟩ := henv.operands hargs'
        obtain ⟨g, p, hg, hen, hm⟩ := hcalls.callee_allowed hmono hg' hr hS (p' := (_, _)) hen'
          (fun hgm hbm env env' h T T' hT e' he' => ihn _ env env' _ T T' hgm hbm h hT e' he') hx
          (fun _ h => nomatch h) (fun h => nomatch h)
        rcases hm with ⟨N, r, hN⟩ | ⟨N₁, ⟨vs, T⟩, k, hx₁, hvs, hT₁⟩
        · exact MemAllowed.of_someUB ⟨N + 1, r, hub (.callUB hreg hargs hT hc hg hen hN)⟩ _
        have hty := (DVals.types_eq_of_isRefinedBy hvs).trans hty'
        have hlen := hlen'.trans (DVals.length_eq_of_isRefinedBy hvs).symm
        have hm := ih _ (Nat.lt_succ_of_le (Nat.min_le_right _ _)) _ _ _ _ _ _ hf hops'
          (henv.zip_append _ hvs) hT₁ _ he
        exact MemAllowed.of_step N₁ (fun N₂ x hx hxe h =>
          Func.memCall_cont hreg hargs hT hc hg hen hx₁ hty hlen hx hxe h) hm

end Fir
