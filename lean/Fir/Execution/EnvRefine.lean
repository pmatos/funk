import Fir.Execution.CallSteps

/-!
# Environments whose values refine others

Refined arguments refine a run because the run only passes values on: it
looks them up by name, checks their types and hands them to ops, to
successors and to callees. An environment is refined by another when both
bind the same names in the same order, each to a value that the other's
value refines. A typed value refines only a value of its own type, so
each check of the interpreter decides alike on both. The facts below
follow a step from the refining environment back to the refined one:

* binding values that refine others keeps the relation;
* a value, or the operands of an op, found in the refining environment
  are found in the refined one, refined;
* a jump goes to the same block, and binds environments of which one
  refines the other;
* a function entered on values that refine others starts at the same op,
  in an environment that refines the other's.
-/

namespace Fir

variable {d : Dialect} [TyDenote d.Ty] [TyRefinement d.Ty]

/-- A typed value refines only a value of its own type. -/
theorem DVal.type_eq_of_isRefinedBy {v v' : DVal d} (h : v ⊑ v') : v.1 = v'.1 := h.1

/-- Two lists of typed values, one refining the other, have the same types. -/
theorem DVals.types_eq_of_isRefinedBy : ∀ {vs vs' : List (DVal d)}, vs ⊑ vs' →
    vs.map (·.1) = vs'.map (·.1)
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨h, hs⟩ => by
    simp only [List.map_cons, DVal.type_eq_of_isRefinedBy h, DVals.types_eq_of_isRefinedBy hs]
  | [], _ :: _, h | _ :: _, [], h => h.elim

/-- Two lists of typed values, one refining the other, have the same length. -/
theorem DVals.length_eq_of_isRefinedBy {vs vs' : List (DVal d)} (h : vs ⊑ vs') :
    vs.length = vs'.length := by
  have := congrArg List.length (DVals.types_eq_of_isRefinedBy h)
  simpa using this

/-- The values of two vectors, one refining the other position by position,
refine one by one. -/
theorem HVector.toDVals_isRefinedBy :
    ∀ {ts : List d.Ty} {a a' : HVector toType ts}, a.Forall₂ TyRefinement.IsRefinedBy a' →
      HVector.toDVals a ⊑ HVector.toDVals a'
  | [], .nil, .nil, _ => trivial
  | _ :: _, .cons _ _, .cons _ _, h => ⟨⟨rfl, h.1⟩, HVector.toDVals_isRefinedBy h.2⟩

/-- An environment refined by another: the same names, in the same order,
each bound to a value that the other's value refines. -/
def Env.IsRefinedBy : Env d → Env d → Prop
  | [], [] => True
  | (x, v) :: env, (x', v') :: env' => x = x' ∧ v ⊑ v' ∧ Env.IsRefinedBy env env'
  | _, _ => False

/-- Binding names to values that refine others refines the environment. -/
theorem Env.IsRefinedBy.zip_append {env env' : Env d} (h : env.IsRefinedBy env') :
    ∀ (xs : List Name) {vs vs' : List (DVal d)}, vs ⊑ vs' →
      Env.IsRefinedBy (xs.zip vs ++ env) (xs.zip vs' ++ env')
  | [], _, _, _ => by simpa using h
  | _ :: _, [], [], _ => by simpa using h
  | x :: xs, _ :: _, _ :: _, ⟨hv, hvs⟩ => ⟨rfl, hv, Env.IsRefinedBy.zip_append h xs hvs⟩
  | _ :: _, [], _ :: _, hv | _ :: _, _ :: _, [], hv => hv.elim

/-- A name bound in the refining environment is bound in the refined one, to
a value that its value refines. -/
theorem Env.IsRefinedBy.lookup {x : Name} :
    ∀ {env env' : Env d}, env.IsRefinedBy env' → ∀ {v' : DVal d}, env'.lookup x = some v' →
      ∃ v, env.lookup x = some v ∧ v ⊑ v'
  | [], [], _, _, h => nomatch h
  | (y, v) :: env, (y', v') :: env', ⟨hy, hv, hr⟩, _, h => by
    subst hy
    by_cases hx : x = y
    · subst hx
      simp only [List.lookup, beq_self_eq_true] at h ⊢
      cases h
      exact ⟨v, rfl, hv⟩
    · have hb : (x == y) = false := beq_false_of_ne hx
      simp only [List.lookup, hb] at h ⊢
      exact Env.IsRefinedBy.lookup hr h
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => h.elim

/-- A value found in the refining environment is found in the refined one,
refined. -/
theorem Env.IsRefinedBy.value {env env' : Env d} (h : env.IsRefinedBy env') {x : Name}
    {v' : DVal d} (hv : env'.value x = .ok v') : ∃ v, env.value x = .ok v ∧ v ⊑ v' := by
  simp only [Env.value] at hv ⊢
  split at hv
  · rename_i w hw
    cases hv
    obtain ⟨v, hl, hr⟩ := h.lookup hw
    exact ⟨v, by simp [hl]; rfl, hr⟩
  · cases hv

/-- Values found in the refining environment are found in the refined one,
refined. -/
theorem Env.IsRefinedBy.mapM_value {env env' : Env d} (h : env.IsRefinedBy env') :
    ∀ {xs : List Name} {vs' : List (DVal d)}, xs.mapM env'.value = .ok vs' →
      ∃ vs, xs.mapM env.value = .ok vs ∧ vs ⊑ vs'
  | [], _, hm => by cases hm; exact ⟨[], rfl, trivial⟩
  | x :: xs, vs', hm => by
    simp only [List.mapM_cons] at hm ⊢
    cases hx : env'.value x with
    | error e => rw [hx] at hm; cases hm
    | ok v' =>
      cases hxs : xs.mapM env'.value with
      | error e => rw [hx, hxs] at hm; cases hm
      | ok vs'' =>
        rw [hx, hxs] at hm
        cases hm
        obtain ⟨v, hv, hvr⟩ := h.value hx
        obtain ⟨vs, hvs, hvsr⟩ := Env.IsRefinedBy.mapM_value h hxs
        refine ⟨v :: vs, ?_, hvr, hvsr⟩
        rw [hv, hvs]
        rfl

variable [DecidableEq d.Ty]

omit [TyRefinement d.Ty] in
/-- The operands of an op are found when the first is found with its
type, and so are the rest. -/
theorem Env.operands_cons_ok {env : Env d} {t : d.Ty} {ts : List d.Ty} {x : Name}
    {xs : List Name} {a : HVector toType (t :: ts)} :
    env.operands (t :: ts) (x :: xs) = .ok a ↔
      ∃ v as, env.value x = .ok ⟨t, v⟩ ∧ env.operands ts xs = .ok as ∧ a = .cons v as := by
  simp only [Env.operands]
  constructor
  · intro h
    cases hx : env.value x with
    | error e => rw [hx] at h; cases h
    | ok v =>
      obtain ⟨t', w⟩ := v
      rw [hx] at h
      change (if h : t' = t then _ else _) = _ at h
      split at h
      · rename_i htt
        subst htt
        cases hxs : env.operands ts xs with
        | error e => rw [hxs] at h; cases h
        | ok as => rw [hxs] at h; cases h; exact ⟨w, as, rfl, rfl, rfl⟩
      · cases h
  · rintro ⟨v, as, hx, hxs, rfl⟩
    rw [hx]
    change (if h : t = t then _ else _) = _
    rw [dite_eq_left rfl, hxs]
    rfl

/-- The operands found in the refining environment are found in the refined
one, refined position by position. -/
theorem Env.IsRefinedBy.operands {env env' : Env d} (h : env.IsRefinedBy env') :
    ∀ {ts : List d.Ty} {xs : List Name} {args' : HVector toType ts},
      env'.operands ts xs = .ok args' →
      ∃ args, env.operands ts xs = .ok args ∧ args.Forall₂ TyRefinement.IsRefinedBy args'
  | [], [], _, hm => by cases hm; exact ⟨.nil, rfl, trivial⟩
  | t :: ts, x :: xs, args', hm => by
    obtain ⟨v', as', hx, hxs, rfl⟩ := Env.operands_cons_ok.1 hm
    obtain ⟨⟨t₀, v⟩, hv, ⟨hty, hvr⟩⟩ := h.value hx
    dsimp only at hty
    subst hty
    obtain ⟨as, has, hasr⟩ := Env.IsRefinedBy.operands h hxs
    exact ⟨.cons v as, Env.operands_cons_ok.2 ⟨v, as, hv, has, rfl⟩, hvr, hasr⟩
  | [], _ :: _, _, hm | _ :: _, [], _, hm => by cases hm

omit [TyRefinement d.Ty] in
/-- Where a jump goes, and the environment it binds. -/
theorem Func.jump_eq_ok {f : Func d} {env : Env d} {succs : List Succ} {i : Nat} {b : Block d}
    {env₁ : Env d} (h : f.jump env succs i = .ok (b, env₁)) :
    ∃ s vs, succs[i]? = some s ∧ f.block? s.label = some b ∧ s.args.mapM env.value = .ok vs ∧
      (b.params.map (·.1)).length = vs.length ∧ vs.map (·.1) = b.params.map (·.2) ∧
      env₁ = (b.params.map (·.1)).zip vs ++ env := by
  simp only [Func.jump] at h
  split at h
  · rename_i s hs
    split at h
    · rename_i b' hb
      cases hvs : s.args.mapM env.value with
      | error e => rw [hvs] at h; cases h
      | ok vs =>
        rw [hvs] at h
        change (do let env' ← env.bind _ vs _; if _ then pure (b', env') else stuck _) = _ at h
        simp only [Env.bind] at h
        split at h
        · rename_i hlen
          change (if _ then _ else _) = _ at h
          split at h
          · rename_i hty
            cases h
            exact ⟨s, vs, hs, hb, hvs, hlen, hty, rfl⟩
          · cases h
        · cases h
    · cases h
  · cases h

omit [TyRefinement d.Ty] in
/-- A jump goes to the block that its successor names, with the values it
passes bound to the block's arguments, when they are found and have their
types. -/
theorem Func.jump_of {f : Func d} {env : Env d} {succs : List Succ} {i : Nat} {b : Block d}
    {s : Succ} {vs : List (DVal d)} (hs : succs[i]? = some s) (hb : f.block? s.label = some b)
    (hvs : s.args.mapM env.value = .ok vs) (hlen : (b.params.map (·.1)).length = vs.length)
    (hty : vs.map (·.1) = b.params.map (·.2)) :
    f.jump env succs i = .ok (b, (b.params.map (·.1)).zip vs ++ env) := by
  simp only [Func.jump, hs, hb, hvs]
  change (do let env' ← env.bind _ vs _; if _ then pure (b, env') else stuck _) = _
  rw [Env.bind_ok _ _ hlen]
  change (if _ then _ else _) = _
  rw [ite_eq_left hty]
  rfl

/-- A jump from the refining environment goes where the jump from the
refined one goes, and binds an environment that refines the other's. -/
theorem Env.IsRefinedBy.jump {env env' : Env d} (h : env.IsRefinedBy env') {f : Func d}
    {succs : List Succ} {i : Nat} {b : Block d} {env₁' : Env d}
    (hj : f.jump env' succs i = .ok (b, env₁')) :
    ∃ env₁, f.jump env succs i = .ok (b, env₁) ∧ env₁.IsRefinedBy env₁' := by
  obtain ⟨s, vs', hs, hb, hvs', hlen, hty, rfl⟩ := Func.jump_eq_ok hj
  obtain ⟨vs, hvs, hr⟩ := h.mapM_value hvs'
  have hty' := DVals.types_eq_of_isRefinedBy hr
  exact ⟨_, Func.jump_of hs hb hvs (hlen.trans (DVals.length_eq_of_isRefinedBy hr).symm)
    (hty'.trans hty), h.zip_append _ hr⟩

omit [TyRefinement d.Ty] in
/-- Where a run of a function starts, when it starts. -/
theorem Func.enter_eq_ok {f : Func d} {dvs : List (DVal d)} {p : List (Operation d) × Env d}
    (h : f.enter dvs = .ok p) :
    ∃ e, f.blocks.head? = some e ∧ e.params = [] ∧ dvs.map (·.1) = f.params.map (·.2) ∧
      p = (e.body, (f.params.map (·.1)).zip dvs) := by
  simp only [Func.enter] at h
  split at h
  · rename_i e he
    split at h
    · cases h
    · rename_i hep
      change (if _ then _ else _) = _ at h
      split at h
      · rename_i hty
        cases h
        exact ⟨e, he, by simpa using hep, hty, rfl⟩
      · cases h
  · cases h

/-- A function entered on values that refine others starts where it starts
on those others, in an environment that refines the other's. -/
theorem Func.enter_isRefinedBy {f : Func d} {dvs dvs' : List (DVal d)} (hr : dvs ⊑ dvs')
    {body : List (Operation d)} {genv' : Env d} (h : f.enter dvs' = .ok (body, genv')) :
    ∃ genv, f.enter dvs = .ok (body, genv) ∧ genv.IsRefinedBy genv' := by
  obtain ⟨e, he, hep, hty, hp⟩ := Func.enter_eq_ok h
  cases hp
  have := (Env.IsRefinedBy.zip_append (env := []) (env' := []) trivial (f.params.map (·.1)) hr)
  simp only [List.append_nil] at this
  exact ⟨_, Func.enter_ok he hep ((DVals.types_eq_of_isRefinedBy hr).trans hty), this⟩

end Fir
