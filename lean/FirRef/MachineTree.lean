import FirRef.Machine

/-!
The proof that `FirRef.Machine` computes the spec's tree of a run
(ADR-2026-11-04-2132): `Machine.advance_tree` says that where the machine
stops stands for the spec's tree of the state it starts from. Each case of
`advance` is one case of `Func.runOps`'s definition (`FirRef.Steps`), on
the spec environment of the state's bindings (`Bindings.toEnv`). A step
of the machine may leave bindings whose spec environment is another list,
since a lookup may move `young` into `old` and a bind puts values in front
of `young`; `Machine.runOps_congr` says that the spec's run does not tell
the two apart, since they give every name the same value.
-/

namespace FirRef.Machine

open Fir Bindings

variable {d : Dialect} [TyDenote d.Ty]

theorem same_toEnv {b : Bindings d} {env : Env d} (h : Agrees b env) : Same b.toEnv env :=
  fun x => (lookup_toEnv b x).trans (h x)

theorem map_pair_ok {α : Type} {r : Except Stuck α} {E E' : Env d} {a : α}
    (h : r.map (·, E) = .ok (a, E')) : r = .ok a ∧ E' = E := by
  cases r with
  | error e => cases h
  | ok a' => cases h; exact ⟨rfl, rfl⟩

theorem map_pair_error {α : Type} {r : Except Stuck α} {E : Env d} {e : Stuck}
    (h : r.map (·, E) = .error e) : r = .error e := by
  cases r with
  | error e' => cases h; rfl
  | ok a => cases h

variable [DecidableEq d.Ty]

theorem args_ok {b b' : Bindings d} {ts : List d.Ty} {xs : List Name} {vs : HVector toType ts}
    (ha : b.args ts xs = .ok (vs, b')) :
    b.toEnv.operands ts xs = .ok vs ∧ Same b'.toEnv b.toEnv := by
  have hf := args_fits (agrees_toEnv b) ts xs
  rw [ha] at hf
  obtain ⟨E, hE, h'⟩ := hf.ok
  obtain ⟨hop, rfl⟩ := map_pair_ok hE
  exact ⟨hop, same_toEnv h'⟩

theorem args_error {b : Bindings d} {ts : List d.Ty} {xs : List Name} {e : Stuck}
    (ha : b.args ts xs = .error e) : b.toEnv.operands ts xs = .error e := by
  have hf := args_fits (agrees_toEnv b) ts xs
  rw [ha] at hf
  exact map_pair_error hf.error

variable [DialectSignature d] {ε : Type} [DialectCall d] [DialectDenote d (ChoiceTree ε)]
  {M : Module d}

theorem afterExit_same {n : Nat} {f : Func d} {e₁ e₂ : Env d} (h : Same e₁ e₂) {o : Operation d}
    (args : HVector toType (sig o.op)) :
    afterExit (ε := ε) M n f e₁ o args = afterExit M n f e₂ o args :=
  funext fun x => afterExit_congr (runOps_congr n) f h o args x

theorem afterDenote_same {n : Nat} {f : Func d} {e₁ e₂ : Env d} (h : Same e₁ e₂)
    (o : Operation d) (os : List (Operation d)) :
    afterDenote (ε := ε) M n f e₁ o os = afterDenote M n f e₂ o os :=
  funext fun rs => afterDenote_congr (runOps_congr n) f h o os rs

theorem afterCall_same {n : Nat} {f : Func d} {e₁ e₂ : Env d} (h : Same e₁ e₂)
    (o : Operation d) (os : List (Operation d)) (s : Name) :
    afterCall (ε := ε) M n f e₁ o os s = afterCall M n f e₂ o os s :=
  funext fun r => afterCall_congr (fun m _ => runOps_congr m) f h o os s r

/-- What the machine gives where it stops stands for the spec's tree of the
rest of the run. -/
theorem advance_tree (c : Cur d ε) (st : List (Frame d)) :
    (advance M c st).tree M = tree M c st := by
  fun_induction advance M c st with
  | case1 f env os st =>
    show _ = (kont M st (Func.runOps M 0 f env.toEnv os)).run
    rw [runOps_zero]; exact (kont_fuel M st).symm
  | case2 n f env st =>
    show _ = (kont M st (Func.runOps M (n + 1) f env.toEnv [])).run
    rw [runOps_nil]; exact (kont_error M st _).symm
  | case3 n f env o os st h =>
    show _ = (kont M st (Func.runOps M (n + 1) f env.toEnv (o :: os))).run
    rw [runOps_region h]; exact (kont_error M st _).symm
  | case4 n f env o os st h e ha =>
    show _ = (kont M st (Func.runOps M (n + 1) f env.toEnv (o :: os))).run
    rw [runOps_operands (Bool.of_not_eq_true h) (args_error ha)]; exact (kont_error M st _).symm
  | case5 n f env o os st h args env' ha hT hos =>
    show _ = (kont M st (Func.runOps M (n + 1) f env.toEnv (o :: os))).run
    rw [runOps_follows (Bool.of_not_eq_true h) (args_ok ha).1 hT hos]
    exact (kont_error M st _).symm
  | case6 n f env o os st h args env' ha hT hos ih =>
    rw [ih]
    show (kont M st (ExceptT.lift _ >>= afterExit M n f env'.toEnv o args)).run =
      (kont M st (Func.runOps M (n + 1) f env.toEnv (o :: os))).run
    rw [runOps_exit (Bool.of_not_eq_true h) (args_ok ha).1 hT (Bool.of_not_eq_true hos),
      afterExit_same (args_ok ha).2]
  | case7 n f env o os st h args env' ha hT hc ih =>
    rw [ih]
    show (kont M st (ExceptT.lift _ >>= afterDenote M n f env'.toEnv o os)).run =
      (kont M st (Func.runOps M (n + 1) f env.toEnv (o :: os))).run
    rw [runOps_denote (Bool.of_not_eq_true h) (args_ok ha).1 (Bool.of_not_eq_true hT) hc,
      afterDenote_same (args_ok ha).2]
  | case8 n f env o os st h args env' ha hT s hc hg =>
    show _ = (kont M st (Func.runOps M (n + 1) f env.toEnv (o :: os))).run
    rw [runOps_noFunc (Bool.of_not_eq_true h) (args_ok ha).1 (Bool.of_not_eq_true hT) hc hg]
    exact (kont_error M st _).symm
  | case9 n f env o os st h args env' ha hT s hc g hg e he =>
    show _ = (kont M st (Func.runOps M (n + 1) f env.toEnv (o :: os))).run
    have hf := enter_fits g args
    rw [he] at hf
    rw [runOps_enter (Bool.of_not_eq_true h) (args_ok ha).1 (Bool.of_not_eq_true hT) hc hg hf.error]
    exact (kont_error M st _).symm
  | case10 n f env o os st h args env' ha hT s hc g hg body genv he ih =>
    rw [ih]
    have hf := enter_fits g args
    rw [he] at hf
    obtain ⟨G, hG, hag⟩ := hf.ok
    show (kont M st (Func.runOps M n g genv.toEnv body >>=
        afterCall M n f env'.toEnv o os s)).run =
      (kont M st (Func.runOps M (n + 1) f env.toEnv (o :: os))).run
    rw [runOps_call (Bool.of_not_eq_true h) (args_ok ha).1 (Bool.of_not_eq_true hT) hc hg hG,
      runOps_congr n g _ _ body (same_toEnv hag), afterCall_same (args_ok ha).2]
  | case11 n f env o os st rs env' hb ih =>
    rw [ih]
    obtain ⟨hE, hag⟩ := bindResults_ok (agrees_toEnv env) hb
    show (kont M st (Func.runOps M n f env'.toEnv os)).run =
      (kont M st (afterDenote M n f env.toEnv o os rs)).run
    rw [afterDenote, hE, liftExcept_ok_bind, runOps_congr n f _ _ os (same_toEnv hag)]
  | case12 n f env o os st rs e hb =>
    show _ = (kont M st (afterDenote M n f env.toEnv o os rs)).run
    rw [afterDenote, bindResults_error hb]
    exact (kont_error M st _).symm
  | case13 n f env o os st r => exact (kont_ub M r st).symm
  | case14 n f env o os st e => exact (kont_noOutcome M e st).symm
  | case15 n f env o os st w k =>
    exact (kont_choose M w st fun b => ((Cur.den n f env o os (k b)).denote M).run).symm
  | case16 n f env o args st h ih =>
    rw [ih]
    show _ = (kont M st (afterExit M n f env.toEnv o args .ret)).run
    rw [afterExit, ite_eq_left h]; rfl
  | case17 n f env o args st h =>
    show _ = (kont M st (afterExit M n f env.toEnv o args .ret)).run
    rw [afterExit, ite_eq_right h]; exact (kont_error M st _).symm
  | case18 n f env o args st i b env' hj ih =>
    rw [ih]
    have hf := jump_fits (agrees_toEnv env) f o.succs i
    rw [hj] at hf
    obtain ⟨E, hE, hag⟩ := hf.ok
    show (kont M st (Func.runOps M n f env'.toEnv b.body)).run =
      (kont M st (afterExit M n f env.toEnv o args (.goto i))).run
    rw [afterExit, hE, liftExcept_ok_bind, runOps_congr n f _ _ b.body (same_toEnv hag)]
  | case19 n f env o args st i e hj =>
    have hf := jump_fits (agrees_toEnv env) f o.succs i
    rw [hj] at hf
    show _ = (kont M st (afterExit M n f env.toEnv o args (.goto i))).run
    rw [afterExit, hf.error]; exact (kont_error M st _).symm
  | case20 n f env o args st r => exact (kont_ub M r st).symm
  | case21 n f env o args st e => exact (kont_noOutcome M e st).symm
  | case22 n f env o args st w k =>
    exact (kont_choose M w st fun b => ((Cur.ex n f env o args (k b)).denote M).run).symm
  | case23 vs k => rfl
  | case24 vs k fr st h env' hb ih =>
    rw [ih]
    obtain ⟨hE, hag⟩ := bind_ok (agrees_toEnv fr.env) hb
    show (kont M st (Func.runOps M (min k fr.n) fr.f env'.toEnv fr.os)).run =
      (kont M st (fr.cont M (.ret (vs, k)))).run
    rw [Frame.cont, afterCall, ite_eq_left h, hE, liftExcept_ok_bind,
      runOps_congr _ fr.f _ _ fr.os (same_toEnv hag)]
  | case25 vs k fr st h e hb =>
    show _ = (kont M st (fr.cont M (.ret (vs, k)))).run
    rw [Frame.cont, afterCall, ite_eq_left h, bind_error hb]
    exact (kont_error M st _).symm
  | case26 vs k fr st h =>
    show _ = (kont M st (fr.cont M (.ret (vs, k)))).run
    rw [Frame.cont, afterCall, ite_eq_right h]; exact (kont_error M st _).symm

end FirRef.Machine
