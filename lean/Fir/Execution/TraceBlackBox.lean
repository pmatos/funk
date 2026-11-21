import Fir.Execution.TraceAhead
import Fir.Execution.TraceArgs

/-!
# Two modules in the traced layer, compared call by call

Congruence in the callee compares the traced runs of a function in a source
module with its traced runs in a target module, where one callee's body is
replaced. The theorems with memory share one engine for this
(`Fir.Execution.MemoryBlackBox`); this section gives its traced
counterpart, in a traced layer of marked traces.

* _Traced runs from a given traced state._ A callee runs from the traced
  state its caller reached, and its caller goes on from the one it leaves.
  So a function's traced runs from a traced state return its values with the
  traced state it ends in (`Func.traceFrom`), as its runs from given
  memories do with memory.
* _A traced black box._ A function of the source and a function of the
  target, of the same parameter types, such that on arguments that refine
  others, from traced states that refine others, the traced observable
  behaviour of the target's function, with the traced state it ends in,
  refines that of the source's. Each symbol names the same function in
  both modules, or a traced black box (`TraceCallsRefined`).
* _Allowed at some budget._ The two runs do not go in step: a black box's
  two functions may take different numbers of steps. So a path of the
  target is allowed by a path of the source at some budget, comparing acts,
  not steps: the source hits UB after acts that the target first shows,
  refined, or, for a return, returns values that the target's refine, after
  acts that the target's refine one by one, in a traced state that the
  target's refines.
-/

namespace Fir

open Memory

variable {A B σ V : Type}

/-! # Traced runs from a given traced state -/

/-- How a path of a run ends, with the traced state each return ends in. -/
def TraceEnd.withState : TraceEnd B σ (Except Stuck (Result V)) →
    Except (String × List B) (Except Stuck (Result (V × σ)) × List B)
  | .ok (.ok (.ret v), t, s) => .ok (.ok (.ret (v, s)), t)
  | .ok (.ok .fuelExhausted, t, _) => .ok (.ok .fuelExhausted, t)
  | .ok (.error st, t, _) => .ok (.error st, t)
  | .error u => .error u

/-- A list refined, at each of its places, by the element of another there,
is refined by a prefix of the other. -/
theorem List.isRefinedPrefix_of_getElem? [HRefinement A A] :
    ∀ {l l' : List A}, (∀ (i : Nat) (a : A), l[i]? = some a → ∃ b, l'[i]? = some b ∧ a ⊑ b) →
      List.IsRefinedPrefix l l'
  | [], l', _ => List.isRefinedPrefix_nil l'
  | a :: l, l', h => by
    obtain ⟨b, hb, hab⟩ := h 0 a rfl
    match l', hb with
    | b' :: l', hb =>
      cases hb
      obtain ⟨m, hm, hp⟩ := List.isRefinedPrefix_of_getElem? (l := l) (l' := l')
        fun i x hx => h (i + 1) x hx
      exact ⟨b :: m, ⟨hab, hm⟩, (List.prefix_cons_inj _).2 hp⟩

/-- The acts of two marked traces, one after the other, are the acts of the
first, then those of the second. -/
theorem Step.actsOf_append (mt mt' : List (Step A)) :
    Step.actsOf (mt ++ mt') = Step.actsOf mt ++ Step.actsOf mt' := by
  simp [Step.actsOf]

section

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

/-- Refinement of traced states is transitive. -/
theorem TraceState.isRefinedBy_trans {s s' s'' : TraceState Mem unit} (h : s ⊑ s')
    (h' : s' ⊑ s'') : s ⊑ s'' :=
  ⟨Memories.isRefinedBy_trans h.1 h'.1, h.2.trans h'.2⟩

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (TraceM (Step A) (TraceState Mem unit))]

/-- The traced runs of the function `f` of the module `M` from given traced
states: on each argument vector and from each traced state, its run in the
traced layer of marked traces at each budget, which returns its values with
the traced state it ends in. -/
def Func.traceFrom (M : Module d) (f : Func d) :
    FuncTraceRuns (HVector toType (f.params.map (·.2)) × TraceState Mem unit) A
      (List (DVal d) × TraceState Mem unit) :=
  fun p n o => ∃ e, (f.run M (m := TraceM (Step A) (TraceState Mem unit)) p.1 n).run p.2 e ∧
    o = TraceEnd.withState e

variable {M : Module d} {f : Func d} {a : HVector toType (f.params.map (·.2))}
  {s : TraceState Mem unit} {n : Nat} {mt : List (Step A)}

/-- A return of a function's traced run from a traced state is a return of
its entry block's ops in its frame, whatever steps it leaves; and each such
return is one. -/
theorem Func.traceFrom_ret_iff {vs : List (DVal d)} {s₁ : TraceState Mem unit} :
    f.traceFrom M (a, s) n (.ok (.ok (.ret (vs, s₁)), mt)) ↔
      ∃ body env, f.enter a.toDVals = .ok (body, env) ∧
        ∃ k, Func.traceCall (Step A) M n f env body s (.ok (.ok (.ret (vs, k)), mt, s₁)) := by
  constructor
  · rintro ⟨e, he, ho⟩
    match e, he, ho with
    | .ok (.ok (.ret _), _, _), he, ho =>
      cases ho
      obtain ⟨body, env, hen, e₀, h₀, he₀⟩ := (Func.traceRun_iff (TraceEnd.notStuck_ok _ _ _)).1 he
      match e₀, h₀, he₀ with
      | .ok (.ok (.ret (_, k)), _, _), h₀, he₀ =>
        cases he₀
        exact ⟨body, env, hen, k, h₀⟩
      | .ok (.ok .fuelExhausted, _, _), _, he₀ | .ok (.error _, _, _), _, he₀ | .error _, _, he₀ =>
        cases he₀
    | .ok (.ok .fuelExhausted, _, _), _, ho | .ok (.error _, _, _), _, ho | .error _, _, ho =>
      cases ho
  · rintro ⟨body, env, hen, k, h⟩
    exact ⟨_, (Func.traceRun_iff (TraceEnd.notStuck_ok _ _ _)).2 ⟨body, env, hen, _, h, rfl⟩, rfl⟩

/-- UB of a function's traced run from a traced state is UB of its entry
block's ops in its frame, after the same acts; and each such UB is one. -/
theorem Func.traceFrom_ub_iff {r : String} :
    f.traceFrom M (a, s) n (.error (r, mt)) ↔
      ∃ body env, f.enter a.toDVals = .ok (body, env) ∧
        Func.traceCall (Step A) M n f env body s (.error (r, mt)) := by
  constructor
  · rintro ⟨e, he, ho⟩
    match e, he, ho with
    | .error _, he, ho =>
      cases ho
      obtain ⟨body, env, hen, e₀, h₀, he₀⟩ := (Func.traceRun_iff (TraceEnd.notStuck_error _ _)).1 he
      match e₀, h₀, he₀ with
      | .error _, h₀, he₀ =>
        cases he₀
        exact ⟨body, env, hen, h₀⟩
      | .ok (.ok (.ret _), _, _), _, he₀ | .ok (.ok .fuelExhausted, _, _), _, he₀
      | .ok (.error _, _, _), _, he₀ => cases he₀
    | .ok (.ok (.ret _), _, _), _, ho | .ok (.ok .fuelExhausted, _, _), _, ho
    | .ok (.error _, _, _), _, ho => cases ho
  · rintro ⟨body, env, hen, h⟩
    exact ⟨_, (Func.traceRun_iff (TraceEnd.notStuck_error _ _)).2 ⟨body, env, hen, _, h, rfl⟩, rfl⟩

/-- A path of a function's traced run from a traced state that runs out of
fuel is a path of its entry block's ops in its frame that runs out of fuel
after the same marked trace; and each such path is one. -/
theorem Func.traceFrom_exhausted_iff :
    f.traceFrom M (a, s) n (.ok (.ok .fuelExhausted, mt)) ↔
      ∃ body env s₁, f.enter a.toDVals = .ok (body, env) ∧
        Func.traceCall (Step A) M n f env body s (.ok (.ok .fuelExhausted, mt, s₁)) := by
  constructor
  · rintro ⟨e, he, ho⟩
    match e, he, ho with
    | .ok (.ok .fuelExhausted, _, s₁), he, ho =>
      cases ho
      obtain ⟨body, env, hen, e₀, h₀, he₀⟩ := (Func.traceRun_iff (TraceEnd.notStuck_ok _ _ _)).1 he
      match e₀, h₀, he₀ with
      | .ok (.ok .fuelExhausted, _, _), h₀, he₀ =>
        cases he₀
        exact ⟨body, env, s₁, hen, h₀⟩
      | .ok (.ok (.ret _), _, _), _, he₀ | .ok (.error _, _, _), _, he₀ | .error _, _, he₀ =>
        cases he₀
    | .ok (.ok (.ret _), _, _), _, ho | .ok (.error _, _, _), _, ho | .error _, _, ho =>
      cases ho
  · rintro ⟨body, env, s₁, hen, h⟩
    exact ⟨_, (Func.traceRun_iff (TraceEnd.notStuck_ok _ _ _)).2 ⟨body, env, hen, _, h, rfl⟩, rfl⟩

end

/-! # Allowed at some budget -/

section

variable [HRefinement A A] {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem] [HRefinement V V]

/-- A source run hits UB at some budget after acts that the marked trace
`mt'` first shows, refined. -/
def TSomeUB (src : Nat → Paths (TraceEnd (Step A) (TraceState Mem unit) (Except Stuck (Result (V × Nat)))))
    (mt' : List (Step A)) : Prop :=
  ∃ N r mt, src N (.error (r, mt)) ∧ List.IsRefinedPrefix (Step.actsOf mt) (Step.actsOf mt')

/-- The source `src`, a run at each budget, allows the target's path at some
budget: it hits UB after acts that the target's path first shows, refined,
which allows anything that shows them; or, for a return, it returns at some
budget values that the target's refine, after acts that the target's refine
one by one, in a traced state that the target's refines. A path that runs
out of fuel or is stuck asks nothing here. -/
def TAllowed (src : Nat → Paths (TraceEnd (Step A) (TraceState Mem unit) (Except Stuck (Result (V × Nat))))) :
    TraceEnd (Step A) (TraceState Mem unit) (Except Stuck (Result (V × Nat))) → Prop
  | .ok (.ok (.ret (v', _)), mt', s') => TSomeUB src mt' ∨
      ∃ N v k mt s, src N (.ok (.ok (.ret (v, k)), mt, s)) ∧ v ⊑ v' ∧
        Step.actsOf mt ⊑ Step.actsOf mt' ∧ s ⊑ s'
  | .error (_, mt') => TSomeUB src mt'
  | _ => True

variable {src c : Nat → Paths (TraceEnd (Step A) (TraceState Mem unit) (Except Stuck (Result (V × Nat))))}

/-- UB at some budget after acts that a path first shows allows it. -/
theorem TAllowed.of_someUB {e' : TraceEnd (Step A) (TraceState Mem unit) (Except Stuck (Result (V × Nat)))}
    (h : TSomeUB src (TraceEnd.trace e')) : TAllowed src e' := by
  rcases e' with ⟨_, _⟩ | ⟨_ | (_ | _), _, _⟩
  · exact h
  · trivial
  · exact .inl h
  · trivial

/-- A path allowed by the rest of a run is allowed by the whole, after acts
that refine the target's first acts one by one, when every way that the rest
ends at the budget `N`, done, is a way that the whole ends at `N₀ + N + 1`,
after the marked trace `t`, with `k` more steps left on a return. -/
theorem TAllowed.of_step {k N₀ : Nat} {t t' : List (Step A)} (ht : Step.actsOf t ⊑ Step.actsOf t')
    (hstep : ∀ N x, TraceEnd.Done x → c N x → src (N₀ + N + 1) ((x.addLeft k).after t))
    {e' : TraceEnd (Step A) (TraceState Mem unit) (Except Stuck (Result (V × Nat)))} :
    TAllowed c e' → TAllowed src (e'.after t') := by
  have ub : ∀ {mt'}, TSomeUB c mt' → TSomeUB src (t' ++ mt') := fun ⟨N, r, mt, h, hle⟩ =>
    ⟨_, r, t ++ mt, hstep N (.error (r, mt)) (by exact trivial) h, by
      rw [Step.actsOf_append, Step.actsOf_append]; exact hle.append_left ht⟩
  rcases e' with ⟨_, _⟩ | ⟨_ | (⟨_, _⟩ | _), _, _⟩
  · exact ub
  · exact fun _ => trivial
  · rintro (h | ⟨N, v, i, mt, s, h, hv, hmt, hs⟩)
    · exact .inl (ub h)
    · refine .inr ⟨_, v, i + k, t ++ mt, s, hstep N _ (by exact trivial) h, hv, ?_, hs⟩
      rw [Step.actsOf_append, Step.actsOf_append]
      exact List.IsRefinedBy.append ht hmt
  · exact fun _ => trivial

end

/-! # A call's frame -/

section

variable [HRefinement A A] {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (TraceM (Step A) (TraceState Mem unit))] [TyRefinement d.Ty]

/-- A path of a callee in the target's frame, done, is allowed by the
source's callee in its frame, from traced states of which the target's
refines the source's, when each path of the target's callee's ops from the
traced state with a frame entered is allowed by the source's: leaving a
frame keeps refinement. -/
theorem Func.traceCall_tAllowed {M M' : Module d} {n : Nat} {g g' : Func d} {genv genv' : Env d}
    {body body' : List (Operation d)} {s s' : TraceState Mem unit}
    (h : ∀ e₀, Func.traceOps (Step A) M' n g' genv' body' { s' with mem := s'.mem.enter } e₀ →
      TAllowed (fun N => Func.traceOps (Step A) M N g genv body { s with mem := s.mem.enter }) e₀)
    {e' : TraceEnd (Step A) (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))}
    (he' : Func.traceCall (Step A) M' n g' genv' body' s' e') :
    TAllowed (fun N => Func.traceCall (Step A) M N g genv body s) e' := by
  have ub : ∀ {mt'}, TSomeUB (fun N => Func.traceOps (Step A) M N g genv body
      { s with mem := s.mem.enter }) mt' →
      TSomeUB (fun N => Func.traceCall (Step A) M N g genv body s) mt' :=
    fun ⟨N, r, mt, hN, hle⟩ => ⟨N, r, mt, (TraceM.run_inFrame _ _ _).2 ⟨_, hN, rfl⟩, hle⟩
  obtain ⟨e₀, h₀, rfl⟩ := (TraceM.run_inFrame _ _ _).1 he'
  have ha := h e₀ h₀
  rcases e₀ with ⟨_, _⟩ | ⟨_ | (⟨_, _⟩ | _), _, _⟩
  · exact ub ha
  · trivial
  · rcases ha with hu | ⟨N, v, k, mt, s₁, hN, hv, hmt, hs⟩
    · exact .inl (ub hu)
    · exact .inr ⟨N, v, k, mt, _, (TraceM.run_inFrame _ _ _).2 ⟨_, hN, rfl⟩, hv, hmt,
        TraceState.IsRefinedBy.exit hs⟩
  · trivial

/-! # Traced black boxes -/

/-- A traced black box: the function `g` of the source module `M`, whose
calls the target module `M'` runs as calls of `g'`. Their parameters have
the same types; on arguments that refine others, from traced states that
refine others, the traced behaviour of `g'` refines that of `g`, the traced
states they end in included. -/
structure TraceBlackBox (M M' : Module d) (g g' : Func d) : Prop where
  params : g'.params.map (·.2) = g.params.map (·.2)
  refines : ∀ (a a' : HVector toType (g.params.map (·.2))) (s s' : TraceState Mem unit),
    a.Forall₂ TyRefinement.IsRefinedBy a' → s ⊑ s' →
      traceObservable (g.traceFrom (A := A) M (a, s)) ⊑
        traceObservable (g'.traceFrom (A := A) M' (a'.cast params.symm, s'))

variable (A Mem unit) in
/-- The target module `M'` runs each call in the traced layer as the source
`M` does: each symbol names the same function in both, or a traced black
box. -/
def TraceCallsRefined (M M' : Module d) : Prop :=
  ∀ s, M'.func? s = M.func? s ∨
    ∃ g g', M.func? s = some g ∧ M'.func? s = some g' ∧
      TraceBlackBox (A := A) (Mem := Mem) (unit := unit) M M' g g'

/-- A call that enters a black box's target passes arguments of the
parameter types of the black box's source. -/
theorem TraceBlackBox.sig {M M' : Module d} {g g' : Func d}
    (bb : TraceBlackBox (A := A) (Mem := Mem) (unit := unit) M M' g g') {ts : List d.Ty}
    {args' : HVector toType ts} {p : List (Operation d) × Env d}
    (hen' : g'.enter args'.toDVals = .ok p) : ts = g.params.map (·.2) := by
  obtain ⟨_, _, _, hty', _⟩ := Func.enter_eq_ok hen'
  rw [HVector.toDVals_types] at hty'
  exact hty'.trans bb.params

/-- A return or UB of a black box's target in its frame, called on arguments
that refine the source's from a traced state that refines the source's, is
allowed by the source's callee in its frame, which starts. -/
theorem TraceBlackBox.allowed {M M' : Module d} {g g' : Func d}
    (bb : TraceBlackBox (A := A) (Mem := Mem) (unit := unit) M M' g g') {ts : List d.Ty}
    {args args' : HVector toType ts} (hr : args.Forall₂ TyRefinement.IsRefinedBy args')
    {s s' : TraceState Mem unit} (hs : s ⊑ s') {n : Nat} {p' : List (Operation d) × Env d}
    (hen' : g'.enter args'.toDVals = .ok p')
    {e' : TraceEnd (Step A) (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))}
    (he' : Func.traceCall (Step A) M' n g' p'.2 p'.1 s' e') (hd : e'.Done) :
    ∃ p, g.enter args.toDVals = .ok p ∧
      TAllowed (fun N => Func.traceCall (Step A) M N g p.2 p.1 s) e' := by
  have hsig := bb.sig hen'
  have href := bb.refines _ _ s s' (HVector.forall₂_cast hsig hr) hs
  have hcast : ((args.cast hsig) : HVector toType _).toDVals = args.toDVals := HVector.toDVals_cast _ _
  have hcast' : ((args'.cast hsig).cast bb.params.symm : HVector toType _).toDVals = args'.toDVals := by
    rw [HVector.toDVals_cast, HVector.toDVals_cast]
  have hen'' : g'.enter ((args'.cast hsig).cast bb.params.symm).toDVals = .ok (p'.1, p'.2) :=
    hcast' ▸ hen'
  -- The source's UB, as a path of its callee in its frame.
  have ub : ∀ {tr r mt'}, traceObservable (g.traceFrom (A := A) M (args.cast hsig, s)) (.ub tr r) →
      (∀ (i : Nat) (a : A), tr[i]? = some a → ∃ b, (Step.actsOf mt')[i]? = some b ∧ a ⊑ b) →
      ∃ p, g.enter args.toDVals = .ok p ∧
        TSomeUB (fun N => Func.traceCall (Step A) M N g p.2 p.1 s) mt' := by
    rintro tr r mt' ⟨N, mt, hN, rfl⟩ hsh
    obtain ⟨body, env, hen, h⟩ := Func.traceFrom_ub_iff.1 hN
    exact ⟨(body, env), hcast ▸ hen, N, r, mt, h, List.isRefinedPrefix_of_getElem? hsh⟩
  rcases e' with ⟨r', mt'⟩ | ⟨_ | (⟨vs', k'⟩ | _), mt', s₁'⟩
  · obtain ⟨t, ht, hle⟩ := href (.ub (Step.actsOf mt') r')
      ⟨n, mt', Func.traceFrom_ub_iff.2 ⟨_, _, hen'', he'⟩, rfl⟩
    match t, ht, hle with
    | .ub tr r, ht, hle => exact ub ht fun i a ha => hle i a ha
    | .ret _ _, _, hle | .diverge _, _, hle | .reacts _, _, hle => exact (hle : False).elim
  · exact hd.elim
  · obtain ⟨t, ht, hle⟩ := href (.ret (Step.actsOf mt') (vs', s₁'))
      ⟨n, mt', Func.traceFrom_ret_iff.2 ⟨_, _, hen'', k', he'⟩, rfl⟩
    match t, ht, hle with
    | .ub tr r, ht, hle =>
      obtain ⟨p, hp, hu⟩ := ub (mt' := mt') ht fun i a ha => hle i a ha
      exact ⟨p, hp, .inl hu⟩
    | .ret tr ⟨vs, s₁⟩, ht, hle =>
      obtain ⟨N, mt, hN, htr⟩ := ht
      obtain ⟨body, env, hen, k, h⟩ := Func.traceFrom_ret_iff.1 hN
      subst htr
      exact ⟨(body, env), hcast ▸ hen, .inr ⟨N, vs, k, mt, s₁, h, hle.2.1, hle.1, hle.2.2⟩⟩
    | .diverge _, _, hle | .reacts _, _, hle => exact (hle : False).elim
  · exact hd.elim

end

end Fir
