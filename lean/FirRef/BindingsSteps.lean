import FirRef.Bindings

/-!
Each operation of `FirRef.Bindings` gives what the spec's operation on an
environment gives (`Fits`): the same error, with the same message, or the
same values, with bindings that give every name what the spec's new
environment gives it. Lookups (`value`, `operands`, `args`, `values`) may
move `young` into `old`, binds (`bind`, `bindResults`) put new values in
front of `young`, and `jump` and `enter` are `Func.jump` and `Func.enter`
on bindings.
-/

namespace FirRef.Bindings

open Fir

theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

theorem error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl

theorem map_ok {ε α β : Type} (f : α → β) (a : α) : (Except.ok a : Except ε α).map f = .ok (f a) :=
  rfl

theorem map_error {ε α β : Type} (f : α → β) (e : ε) :
    (Except.error e : Except ε α).map f = .error e := rfl

theorem pure_ok {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

variable {d : Dialect} [TyDenote d.Ty]

/-- What an operation on bindings gives fits what the spec's operation
gives: the same error, or the same value, with bindings that agree with
the spec's environment. -/
def Fits {α : Type} : Except Stuck (α × Bindings d) → Except Stuck (α × Env d) → Prop
  | .ok (a, b), .ok (a', e) => a = a' ∧ Agrees b e
  | .error e, .error e' => e = e'
  | _, _ => False

theorem Fits.ok {α : Type} {a : α} {b : Bindings d} {r : Except Stuck (α × Env d)}
    (h : Fits (.ok (a, b)) r) : ∃ e, r = .ok (a, e) ∧ Agrees b e := by
  match r, h with
  | .ok (_, e), ⟨rfl, h⟩ => exact ⟨e, rfl, h⟩

theorem Fits.error {α : Type} {e : Stuck} {r : Except Stuck (α × Env d)}
    (h : Fits (.error e) r) : r = .error e := by
  match r, h with
  | .error _, rfl => rfl

theorem value_fits {b : Bindings d} {env : Env d} (h : Agrees b env) (x : Name) :
    Fits (b.value x) ((env.value x).map (·, env)) := by
  have hg := (look_val b x).trans (h x)
  unfold value Env.value
  revert hg
  cases look b x with
  | hit v k =>
    intro hg
    rw [← hg]
    exact ⟨rfl, fun y => (get_pay b _ y).trans (h y)⟩
  | miss =>
    intro hg
    rw [← hg]
    rfl

theorem agrees_push {b : Bindings d} {env : Env d} (h : Agrees b env) (l : Env d) (c : Nat) :
    Agrees { b with young := l.reverse.reverseAux b.young, count := c } (l ++ env) := fun x => by
  simp only [get, List.reverseAux_eq, List.reverse_reverse, List.lookup_append, Option.or_assoc]
  rw [← h x]
  rfl

theorem zipRev_eq : ∀ (rs : List (Name × d.Ty)) (vs : List (DVal d)) (acc : List (Name × DVal d)),
    zipRev rs vs acc =
      if rs.length = vs.length then some (((rs.map (·.1)).zip vs).reverse ++ acc) else none
  | [], [], _ => by simp [zipRev]
  | [], _ :: _, _ => by simp [zipRev]
  | _ :: _, [], _ => by simp [zipRev]
  | (x, t) :: rs, v :: vs, acc => by
    rw [zipRev, zipRev_eq rs vs]
    simp

theorem bind_ok {b b' : Bindings d} {env : Env d} (h : Agrees b env) {rs : List (Name × d.Ty)}
    {vs : List (DVal d)} {why : String} (hb : b.bind rs vs why = .ok b') :
    env.bind (rs.map (·.1)) vs why = .ok ((rs.map (·.1)).zip vs ++ env) ∧
      Agrees b' ((rs.map (·.1)).zip vs ++ env) := by
  unfold bind at hb
  rw [zipRev_eq] at hb
  by_cases hl : rs.length = vs.length
  · simp only [hl, ite_true, List.append_nil, pure_ok, Except.ok.injEq] at hb
    subst hb
    refine ⟨?_, agrees_push h _ _⟩
    simp [Env.bind, hl]
    rfl
  · simp [hl, stuck] at hb

theorem bind_error {b : Bindings d} {env : Env d} {rs : List (Name × d.Ty)} {vs : List (DVal d)}
    {why : String} {e : Stuck} (hb : b.bind rs vs why = .error e) :
    env.bind (rs.map (·.1)) vs why = .error e := by
  unfold bind at hb
  rw [zipRev_eq] at hb
  by_cases hl : rs.length = vs.length
  · simp [hl, pure_ok] at hb
  · simp only [hl, ite_false, stuck, Except.error.injEq] at hb
    subst hb
    simp [Env.bind, hl, stuck]

theorem zipRevH_eq : ∀ (rs : List (Name × d.Ty)) {ts : List d.Ty} (vs : HVector toType ts)
    (acc : List (Name × DVal d)),
    zipRevH rs vs acc = if rs.length = (HVector.toDVals vs).length then
      some (((rs.map (·.1)).zip (HVector.toDVals vs)).reverse ++ acc) else none
  | [], _, .nil, _ => by simp [zipRevH, HVector.toDVals]
  | [], _, .cons _ _, _ => by simp [zipRevH, HVector.toDVals]
  | _ :: _, _, .nil, _ => by simp [zipRevH, HVector.toDVals]
  | (x, t) :: rs, _, .cons v vs, acc => by
    rw [zipRevH, zipRevH_eq rs vs]
    simp [HVector.toDVals]

theorem bindResults_ok {b b' : Bindings d} {env : Env d} (h : Agrees b env)
    {rs : List (Name × d.Ty)} {ts : List d.Ty} {vs : HVector toType ts} {why : String}
    (hb : b.bindResults rs vs why = .ok b') :
    env.bind (rs.map (·.1)) vs.toDVals why = .ok ((rs.map (·.1)).zip vs.toDVals ++ env) ∧
      Agrees b' ((rs.map (·.1)).zip vs.toDVals ++ env) := by
  unfold bindResults at hb
  rw [zipRevH_eq] at hb
  by_cases hl : rs.length = (HVector.toDVals vs).length
  · simp only [hl, ite_true, List.append_nil, pure_ok, Except.ok.injEq] at hb
    subst hb
    refine ⟨?_, agrees_push h _ _⟩
    simp [Env.bind, hl]
    rfl
  · simp [hl, stuck] at hb

theorem bindResults_error {b : Bindings d} {env : Env d} {rs : List (Name × d.Ty)}
    {ts : List d.Ty} {vs : HVector toType ts} {why : String} {e : Stuck}
    (hb : b.bindResults rs vs why = .error e) :
    env.bind (rs.map (·.1)) vs.toDVals why = .error e := by
  unfold bindResults at hb
  rw [zipRevH_eq] at hb
  by_cases hl : rs.length = (HVector.toDVals vs).length
  · simp [hl, pure_ok] at hb
  · simp only [hl, ite_false, stuck, Except.error.injEq] at hb
    subst hb
    simp [Env.bind, hl, stuck]

variable [DecidableEq d.Ty]

theorem operands_fits : ∀ {b : Bindings d} {env : Env d} (_ : Agrees b env)
    (ts : List d.Ty) (xs : List Name),
    Fits (b.operands ts xs) ((env.operands ts xs).map (·, env))
  | _, _, h, [], [] => ⟨rfl, h⟩
  | _, _, _, [], _ :: _ => rfl
  | _, _, _, _ :: _, [] => rfl
  | b, env, h, t :: ts, x :: xs => by
    have hv := value_fits h x
    simp only [operands, Env.operands]
    revert hv
    cases b.value x with
    | error e =>
      cases env.value x with
      | error e' => intro hv; cases hv; rfl
      | ok w => intro hv; exact hv.elim
    | ok p =>
      obtain ⟨⟨t', v⟩, b₁⟩ := p
      cases env.value x with
      | error e => intro hv; exact hv.elim
      | ok w =>
        intro hv
        obtain ⟨rfl, h₁⟩ := hv
        simp only [ok_bind]
        by_cases ht : t' = t
        · subst ht
          simp only [dite_true]
          have ih := operands_fits h₁ ts xs
          revert ih
          cases b₁.operands ts xs with
          | error e =>
            cases env.operands ts xs with
            | error e' => intro ih; cases ih; rfl
            | ok w => intro ih; exact ih.elim
          | ok q =>
            obtain ⟨vs, b₂⟩ := q
            cases env.operands ts xs with
            | error e => intro ih; exact ih.elim
            | ok w =>
              intro ih
              obtain ⟨rfl, h₂⟩ := ih
              exact ⟨rfl, h₂⟩
        · simp only [ht, dite_false]
          rfl

theorem lookOperands_ok {b : Bindings d} {env : Env d} (h : Agrees b env) :
    ∀ (ts : List d.Ty) (xs : List Name) (c : Nat) {vs : HVector toType ts} {c' : Nat},
      b.lookOperands ts xs c = .ok vs c' → env.operands ts xs = .ok vs
  | [], [], _, _, _, hn => by
    simp only [lookOperands, Looked.ok.injEq] at hn
    obtain ⟨rfl, -⟩ := hn
    rfl
  | [], _ :: _, _, _, _, hn => by simp [lookOperands] at hn
  | _ :: _, [], _, _, _, hn => by simp [lookOperands] at hn
  | t :: ts, x :: xs, c, vs, c', hn => by
    have hg := (look_val b x).trans (h x)
    simp only [lookOperands] at hn
    revert hn hg
    cases look b x with
    | miss => intro hn; cases hn
    | hit p k =>
      obtain ⟨t', v⟩ := p
      intro hn hg
      have hev : env.value x = .ok ⟨t', v⟩ := by
        unfold Env.value
        rw [← hg]
        rfl
      simp only [Env.operands, hev, ok_bind]
      by_cases ht : t' = t
      · subst ht
        simp only [dite_true] at hn ⊢
        revert hn
        cases hr : b.lookOperands ts xs (c + cost k) with
        | fail => intro hn; cases hn
        | ok vs' c'' =>
          intro hn
          simp only [Looked.ok.injEq] at hn
          obtain ⟨rfl, -⟩ := hn
          rw [lookOperands_ok h ts xs _ hr]
          rfl
      · simp only [ht, dite_false] at hn
        cases hn

theorem args_fits {b : Bindings d} {env : Env d} (h : Agrees b env) (ts : List d.Ty)
    (xs : List Name) : Fits (b.args ts xs) ((env.operands ts xs).map (·, env)) := by
  unfold args
  cases hn : b.lookOperands ts xs 0 with
  | ok vs c =>
    rw [lookOperands_ok h ts xs 0 hn]
    exact ⟨rfl, fun y => (get_pay b c y).trans (h y)⟩
  | fail => exact operands_fits h ts xs

omit [DecidableEq d.Ty] in
theorem values_fits : ∀ {b : Bindings d} {env : Env d} (_ : Agrees b env) (xs : List Name)
    (acc : List (DVal d)),
    Fits (b.values xs acc) ((xs.mapM env.value).map (fun vs => (acc.reverse ++ vs, env)))
  | _, _, h, [], acc => ⟨by simp, h⟩
  | b, env, h, x :: xs, acc => by
    have hv := value_fits h x
    rw [List.mapM_cons]
    unfold values
    revert hv
    cases b.value x with
    | error e =>
      cases env.value x with
      | error e' => intro hv; cases hv; rfl
      | ok w => intro hv; exact hv.elim
    | ok p =>
      obtain ⟨v, b₁⟩ := p
      cases env.value x with
      | error e => intro hv; exact hv.elim
      | ok w =>
        intro hv
        obtain ⟨rfl, h₁⟩ := hv
        have ih := values_fits h₁ xs (v :: acc)
        simp only [ok_bind]
        revert ih
        cases b₁.values xs (v :: acc) with
        | error e =>
          cases xs.mapM env.value with
          | error e' => intro ih; cases ih; rfl
          | ok w => intro ih; exact ih.elim
        | ok q =>
          cases xs.mapM env.value with
          | error e => intro ih; exact ih.elim
          | ok vs =>
            intro ih
            obtain ⟨vs', b₂⟩ := q
            obtain ⟨rfl, h₂⟩ := ih
            exact ⟨by simp, h₂⟩

theorem jump_fits {b : Bindings d} {env : Env d} (h : Agrees b env) (f : Func d)
    (succs : List Succ) (i : Nat) : Fits (b.jump f succs i) (f.jump env succs i) := by
  unfold jump Func.jump
  cases succs[i]? with
  | none => rfl
  | some s =>
    dsimp only
    cases f.block? s.label with
    | none => rfl
    | some blk =>
      dsimp only
      have hv := values_fits h s.args []
      revert hv
      cases b.values s.args [] with
      | error e =>
        cases s.args.mapM env.value with
        | error e' => intro hv; cases hv; rfl
        | ok w => intro hv; exact hv.elim
      | ok p =>
        obtain ⟨vs, b₁⟩ := p
        cases s.args.mapM env.value with
        | error e => intro hv; exact hv.elim
        | ok w =>
          intro hv
          obtain ⟨hw, h₁⟩ := hv
          simp only [List.reverse_nil, List.nil_append] at hw
          subst hw
          simp only [ok_bind]
          cases hb : b₁.bind blk.params vs
            s!"^{s.label} takes a number of arguments other than its successor passes" with
          | error e =>
            rw [bind_error hb]
            rfl
          | ok b' =>
            obtain ⟨he, h'⟩ := bind_ok h₁ hb
            rw [he]
            simp only [ok_bind]
            split
            · exact ⟨rfl, h'⟩
            · rfl

theorem zipParams_eq : ∀ (ps : List (Name × d.Ty)) {ts : List d.Ty} (vs : HVector toType ts)
    (acc : List (Name × DVal d)),
    zipParams ps vs acc = if (HVector.toDVals vs).map (·.1) = ps.map (·.2) then
      some (((ps.map (·.1)).zip (HVector.toDVals vs)).reverse ++ acc) else none
  | [], _, .nil, _ => by simp [zipParams, HVector.toDVals]
  | [], _, .cons _ _, _ => by simp [zipParams, HVector.toDVals]
  | _ :: _, _, .nil, _ => by simp [zipParams, HVector.toDVals]
  | (x, p) :: ps, t :: _, .cons v vs, acc => by
    rw [zipParams]
    by_cases hp : p = t
    · subst hp
      simp only [↓reduceIte]
      rw [zipParams_eq ps vs]
      simp [HVector.toDVals]
    · simp only [hp, ↓reduceIte]
      simp [HVector.toDVals, Ne.symm hp]

theorem enter_fits (f : Func d) {ts : List d.Ty} (vs : HVector toType ts) :
    Fits (Bindings.enter f vs) (f.enter (HVector.toDVals vs)) := by
  unfold Bindings.enter Func.enter
  cases f.blocks.head? with
  | none => rfl
  | some entry =>
    dsimp only
    by_cases he : (!entry.params.isEmpty) = true
    · simp only [he, ite_true]
      rfl
    · simp only [he, Bool.false_eq_true, ↓reduceIte]
      rw [zipParams_eq]
      by_cases ht : (HVector.toDVals vs).map (·.1) = f.params.map (·.2)
      · simp only [ht, ↓reduceIte, List.append_nil, List.reverse_reverse]
        exact ⟨rfl, fun x => by simp [get]⟩
      · simp only [ht, ↓reduceIte]
        rfl

end FirRef.Bindings
