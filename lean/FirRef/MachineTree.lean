import FirRef.Machine

/-!
The proof that `FirRef.Machine` computes the spec's tree of a run with memory
(`docs/decisions/fir-ref-fast-paths.md#running`,
`docs/decisions/fir-ref-memory.md#the-machine-carries-the-memories`):
`Machine.advance_tree` says that where the machine stops stands for the spec's
tree of the state it starts from. Each case of `advance` is one case of
`Func.runOps`'s definition (`FirRef.Steps`), on the spec environment of the
state's bindings (`Bindings.toEnv`). A step of the machine may leave bindings
whose spec environment is another list, since a lookup may move `young` into
`old` and a bind puts values in front of `young`; `Machine.runOps_congr` says
that the spec's run does not tell the two apart, since they give every name the
same value.
-/

namespace FirRef.Machine

open Fir Memory Bindings

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

variable [DialectSignature d] {ε : Type} [DialectCall d] {N : Type} [DecidableEq N]
  {unit : N → Nat} [DialectDenote d (StateT (Memories N unit) (ChoiceTree ε))] {M : Module d}

local notation "SM" => StateT (Memories N unit) (ChoiceTree ε)

theorem afterExit_same {n : Nat} {f : Func d} {e₁ e₂ : Env d} (h : Same e₁ e₂) {o : Operation d}
    (args : HVector toType (sig o.op)) :
    afterExit (m := SM) M n f e₁ o args = afterExit M n f e₂ o args :=
  funext fun x => afterExit_congr (runOps_congr n) f h o args x

theorem afterDenote_same {n : Nat} {f : Func d} {e₁ e₂ : Env d} (h : Same e₁ e₂)
    (o : Operation d) (os : List (Operation d)) :
    afterDenote (m := SM) M n f e₁ o os = afterDenote M n f e₂ o os :=
  funext fun rs => afterDenote_congr (runOps_congr n) f h o os rs

theorem afterCall_same {n : Nat} {f : Func d} {e₁ e₂ : Env d} (h : Same e₁ e₂)
    (o : Operation d) (os : List (Operation d)) (s : Name) :
    afterCall (m := SM) M n f e₁ o os s = afterCall M n f e₂ o os s :=
  funext fun r => afterCall_congr (fun j _ => runOps_congr j) f h o os s r

/-- What the machine gives where it stops stands for the spec's tree of the
rest of the run. -/
theorem advance_tree {R : Type} (fin : List (DVal d) → Memories N unit → R)
    (c : Cur d ε (Memories N unit)) (st : List (Frame d)) :
    (advance M fin c st).tree M fin = tree M fin c st := by
  fun_induction advance M fin c st with
  | case1 f env os S st =>
    show _ = endWith fin <$> kont M st (runAt (Func.runOps M 0 f env.toEnv os) S)
    rw [runOps_zero]; exact (kont_fuel M fin st S).symm
  | case2 n f env S st =>
    show _ = endWith fin <$> kont M st (runAt (Func.runOps M (n + 1) f env.toEnv []) S)
    rw [runOps_nil]; exact (kont_error M fin st _ S).symm
  | case3 n f env o os S st h =>
    show _ = endWith fin <$> kont M st (runAt (Func.runOps M (n + 1) f env.toEnv (o :: os)) S)
    rw [runOps_region h]; exact (kont_error M fin st _ S).symm
  | case4 n f env o os S st h e ha =>
    show _ = endWith fin <$> kont M st (runAt (Func.runOps M (n + 1) f env.toEnv (o :: os)) S)
    rw [runOps_operands (Bool.of_not_eq_true h) (args_error ha)]
    exact (kont_error M fin st _ S).symm
  | case5 n f env o os S st h args env' ha hT hos =>
    show _ = endWith fin <$> kont M st (runAt (Func.runOps M (n + 1) f env.toEnv (o :: os)) S)
    rw [runOps_follows (Bool.of_not_eq_true h) (args_ok ha).1 hT hos]
    exact (kont_error M fin st _ S).symm
  | case6 n f env o os S st h args env' ha hT hos ih =>
    rw [ih]
    show endWith fin <$> kont M st (ChoiceTree.bind _ fun p : Exit × Memories N unit =>
        runAt (afterExit M n f env'.toEnv o args p.1) p.2) =
      endWith fin <$> kont M st (runAt (Func.runOps M (n + 1) f env.toEnv (o :: os)) S)
    rw [runOps_exit (Bool.of_not_eq_true h) (args_ok ha).1 hT (Bool.of_not_eq_true hos),
      runAt_lift_bind, afterExit_same (args_ok ha).2]
  | case7 n f env o os S st h args env' ha hT hc ih =>
    rw [ih]
    show endWith fin <$> kont M st
        (ChoiceTree.bind _ fun p : HVector toType (returnTypes o.op) × Memories N unit =>
          runAt (afterDenote M n f env'.toEnv o os p.1) p.2) =
      endWith fin <$> kont M st (runAt (Func.runOps M (n + 1) f env.toEnv (o :: os)) S)
    rw [runOps_denote (Bool.of_not_eq_true h) (args_ok ha).1 (Bool.of_not_eq_true hT) hc,
      runAt_lift_bind, afterDenote_same (args_ok ha).2]
  | case8 n f env o os S st h args env' ha hT s hc ih =>
    rw [ih]
    show endWith fin <$> kont M st (runAt (callAt M n f env'.toEnv o os s args) S) =
      endWith fin <$> kont M st (runAt (Func.runOps M (n + 1) f env.toEnv (o :: os)) S)
    rw [runOps_fixed (Bool.of_not_eq_true h) (args_ok ha).1 (Bool.of_not_eq_true hT) hc,
      callAt_congr (fun j _ => runOps_congr j) f (args_ok ha).2]
  | case9 n f env o os S st h args env' ha hT hc ih =>
    rw [ih]
    show endWith fin <$> kont M st (ChoiceTree.bind _ fun p : Name × Memories N unit =>
        runAt (afterPick M n f env'.toEnv o os args p.1) p.2) =
      endWith fin <$> kont M st (runAt (Func.runOps M (n + 1) f env.toEnv (o :: os)) S)
    rw [runOps_pick (Bool.of_not_eq_true h) (args_ok ha).1 (Bool.of_not_eq_true hT) hc,
      runAt_lift_bind]
    congr 2
    exact congrArg _ (funext fun p => by
      rw [afterPick_congr (fun j _ => runOps_congr j) f (args_ok ha).2])
  | case10 n f env o os s ts cargs S st hg hd =>
    show _ = endWith fin <$> kont M st (runAt (callAt M n f env.toEnv o os s cargs) S)
    rw [callAt_ext hg hd, runAt_lift_bind]
    show _ = endWith fin <$> kont M st (.ub extCallUB)
    rw [kont_ub]; rfl
  | case11 n f env o os s ts cargs S st hg hd =>
    show _ = endWith fin <$> kont M st (runAt (callAt M n f env.toEnv o os s cargs) S)
    rw [callAt_noFunc hg (Bool.of_not_eq_true hd)]
    exact (kont_error M fin st _ S).symm
  | case12 n f env o os s ts cargs S st g hg e he =>
    show _ = endWith fin <$> kont M st (runAt (callAt M n f env.toEnv o os s cargs) S)
    have hf := enter_fits g cargs
    rw [he] at hf
    rw [callAt_enter hg hf.error]
    exact (kont_error M fin st _ S).symm
  | case13 n f env o os s ts cargs S st g hg body genv he ih =>
    rw [ih]
    have hf := enter_fits g cargs
    rw [he] at hf
    obtain ⟨G, hG, hag⟩ := hf.ok
    show endWith fin <$> kont M st ((runAt (Func.runOps M n g genv.toEnv body) S.enter).bind
        (Frame.cont M ⟨n, f, env, o, os, s⟩)) =
      endWith fin <$> kont M st (runAt (callAt M n f env.toEnv o os s cargs) S)
    rw [callAt_call hg hG, runAt_bind, runAt_inFrame, ChoiceTree.bind_assoc,
      runOps_congr n g _ _ body (same_toEnv hag)]
    rfl
  | case14 f env o os args st s S =>
    show _ = endWith fin <$> kont M st (runAt (afterPick M 0 f env.toEnv o os args s) S)
    exact (kont_fuel M fin st S).symm
  | case15 n f env o os args st s S ih =>
    rw [ih]
    rfl
  | case16 n f env o os args st r =>
    show _ = endWith fin <$> kont M st (.ub r)
    rw [kont_ub]; rfl
  | case17 n f env o os args st e =>
    show _ = endWith fin <$> kont M st (.noOutcome e)
    rw [kont_noOutcome]; rfl
  | case18 n f env o os args st w c k =>
    show _ = endWith fin <$> kont M st (.choose w c fun b => _)
    rw [kont_choose]; rfl
  | case19 n f env o os st rs S env' hb ih =>
    rw [ih]
    obtain ⟨hE, hag⟩ := bindResults_ok (agrees_toEnv env) hb
    show endWith fin <$> kont M st (runAt (Func.runOps M n f env'.toEnv os) S) =
      endWith fin <$> kont M st (runAt (afterDenote M n f env.toEnv o os rs) S)
    rw [afterDenote, hE, liftExcept_ok_bind, runOps_congr n f _ _ os (same_toEnv hag)]
  | case20 n f env o os st rs S e hb =>
    show _ = endWith fin <$> kont M st (runAt (afterDenote M n f env.toEnv o os rs) S)
    rw [afterDenote, bindResults_error hb, liftExcept_error_bind]
    exact (kont_error M fin st _ S).symm
  | case21 n f env o os st r =>
    show _ = endWith fin <$> kont M st (.ub r)
    rw [kont_ub]; rfl
  | case22 n f env o os st e =>
    show _ = endWith fin <$> kont M st (.noOutcome e)
    rw [kont_noOutcome]; rfl
  | case23 n f env o os st w c k =>
    show _ = endWith fin <$> kont M st (.choose w c fun b => _)
    rw [kont_choose]; rfl
  | case24 n f env o args st S h ih =>
    rw [ih]
    show _ = endWith fin <$> kont M st (runAt (afterExit M n f env.toEnv o args .ret) S)
    rw [afterExit, ite_eq_left h]; rfl
  | case25 n f env o args st S h =>
    show _ = endWith fin <$> kont M st (runAt (afterExit M n f env.toEnv o args .ret) S)
    rw [afterExit, ite_eq_right h]; exact (kont_error M fin st _ S).symm
  | case26 n f env o args st i S b env' hj ih =>
    rw [ih]
    have hf := jump_fits (agrees_toEnv env) f o.succs i
    rw [hj] at hf
    obtain ⟨E, hE, hag⟩ := hf.ok
    show endWith fin <$> kont M st (runAt (Func.runOps M n f env'.toEnv b.body) S) =
      endWith fin <$> kont M st (runAt (afterExit M n f env.toEnv o args (.goto i)) S)
    rw [afterExit, hE, liftExcept_ok_bind, runOps_congr n f _ _ b.body (same_toEnv hag)]
  | case27 n f env o args st i S e hj =>
    have hf := jump_fits (agrees_toEnv env) f o.succs i
    rw [hj] at hf
    show _ = endWith fin <$> kont M st (runAt (afterExit M n f env.toEnv o args (.goto i)) S)
    rw [afterExit, hf.error, liftExcept_error_bind]; exact (kont_error M fin st _ S).symm
  | case28 n f env o args st r =>
    show _ = endWith fin <$> kont M st (.ub r)
    rw [kont_ub]; rfl
  | case29 n f env o args st e =>
    show _ = endWith fin <$> kont M st (.noOutcome e)
    rw [kont_noOutcome]; rfl
  | case30 n f env o args st w c k =>
    show _ = endWith fin <$> kont M st (.choose w c fun b => _)
    rw [kont_choose]; rfl
  | case31 vs k S => rfl
  | case32 vs k S fr st h env' hb ih =>
    rw [ih]
    obtain ⟨hE, hag⟩ := bind_ok (agrees_toEnv fr.env) hb
    show endWith fin <$> kont M st (runAt (Func.runOps M (min k fr.n) fr.f env'.toEnv fr.os) S.exit) =
      endWith fin <$> kont M st (runAt (afterCall M fr.n fr.f fr.env.toEnv fr.o fr.os fr.s
        (.ret (vs, k))) S.exit)
    rw [afterCall, ite_eq_left h, hE, liftExcept_ok_bind,
      runOps_congr _ fr.f _ _ fr.os (same_toEnv hag)]
  | case33 vs k S fr st h e hb =>
    show _ = endWith fin <$> kont M st (runAt (afterCall M fr.n fr.f fr.env.toEnv fr.o fr.os fr.s
      (.ret (vs, k))) S.exit)
    rw [afterCall, ite_eq_left h, bind_error hb, liftExcept_error_bind]
    exact (kont_error M fin st _ _).symm
  | case34 vs k S fr st h =>
    show _ = endWith fin <$> kont M st (runAt (afterCall M fr.n fr.f fr.env.toEnv fr.o fr.os fr.s
      (.ret (vs, k))) S.exit)
    rw [afterCall, ite_eq_right h]; exact (kont_error M fin st _ _).symm

end FirRef.Machine
