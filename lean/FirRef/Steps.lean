import Fir.Execution.MemoryCallSteps
import Fir.Execution.MemoryModes

/-!
Facts about one step of the spec's interpreter, `Func.runOps`, in any monad,
that `FirRef.Machine` builds on
(`docs/decisions/fir-ref-fast-paths.md#running`). The machine runs them in the
state layer over the tree of choices.

* One equation for each case of `Func.runOps`'s definition. Each says what
  the run does after the step through `afterExit`, `afterDenote`, `callAt`
  or `afterPick`, the spec's computation of the rest of the run after a
  terminator exits, after an op gives its results, at a call of a symbol on
  some arguments, and after an op's rule picks its callee (#235); and
  `callAt` through `afterExt` and `afterCall`, after an external call gives
  its values and after a callee returns.
* A run depends on its environment only through what the environment
  gives each name: `runOps_congr` proves that two environments with the
  same `List.lookup` (`Same`) give the same run. So `fir-ref` may keep an
  environment in any form that gives each name what the spec's list gives
  it (`FirRef.Bindings`).
-/

namespace FirRef.Machine

open Fir

variable {d : Dialect} [TyDenote d.Ty]

/-- Two environments that give every name the same value. -/
def Same (e₁ e₂ : Env d) : Prop := ∀ x, e₁.lookup x = e₂.lookup x

theorem Same.refl (e : Env d) : Same e e := fun _ => rfl

theorem Same.symm {e₁ e₂ : Env d} (h : Same e₁ e₂) : Same e₂ e₁ := fun x => (h x).symm

theorem Same.trans {e₁ e₂ e₃ : Env d} (h₁ : Same e₁ e₂) (h₂ : Same e₂ e₃) : Same e₁ e₃ :=
  fun x => (h₁ x).trans (h₂ x)

theorem Same.append (l : Env d) {e₁ e₂ : Env d} (h : Same e₁ e₂) : Same (l ++ e₁) (l ++ e₂) :=
  fun x => by rw [List.lookup_append, List.lookup_append, h x]

theorem value_congr {e₁ e₂ : Env d} (h : Same e₁ e₂) : e₁.value = e₂.value := by
  funext x
  unfold Env.value
  rw [h x]

/-- Two results of a step that gives an environment agree: the same error,
or the same value with environments that give every name the same value. -/
def Agree {α : Type} : Except Stuck (α × Env d) → Except Stuck (α × Env d) → Prop
  | .ok (a, e₁), .ok (b, e₂) => a = b ∧ Same e₁ e₂
  | .error e, .error e' => e = e'
  | _, _ => False

theorem bind_eq (env : Env d) (names : List Name) (vs : List (DVal d)) (why : String) :
    env.bind names vs why =
      if names.length = vs.length then .ok (names.zip vs ++ env) else .error ⟨why⟩ := rfl

variable [DecidableEq d.Ty]

theorem operands_congr {e₁ e₂ : Env d} (h : Same e₁ e₂) :
    ∀ (ts : List d.Ty) (xs : List Name), e₁.operands ts xs = e₂.operands ts xs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | t :: ts, x :: xs => by
    simp only [Env.operands, value_congr h, operands_congr h ts xs]

theorem jump_congr (f : Func d) {e₁ e₂ : Env d} (h : Same e₁ e₂) (succs : List Succ) (i : Nat) :
    Agree (f.jump e₁ succs i) (f.jump e₂ succs i) := by
  unfold Func.jump
  rw [value_congr h]
  cases succs[i]? with
  | none => simp only [Agree, stuck]
  | some s =>
    dsimp only
    cases f.block? s.label with
    | none => simp only [Agree, stuck]
    | some b =>
      dsimp only
      cases s.args.mapM e₂.value with
      | error e => simp only [Agree, bind, Except.bind]
      | ok vs =>
        simp only [bind, Except.bind, bind_eq]
        by_cases hl : (b.params.map (·.1)).length = vs.length
        · by_cases ht : vs.map (·.1) = b.params.map (·.2)
          · simp only [hl, ht, ite_true, Agree, pure, Except.pure, true_and]
            exact Same.append _ h
          · simp only [hl, ht, ite_true, ite_false, Agree, stuck]
        · simp only [hl, ite_false, Agree]

variable [DialectSignature d] [DialectCall d] {m : Type → Type} [Monad m] [MonadFrame m]
  [DialectDenote d m] [DialectExtCall d m]

/-- The spec's computation of the rest of a run of `f` after its
terminator `o`, on the operands `args`, exits to `x`, with `n` steps
left. -/
def afterExit (M : Module d) (n : Nat) (f : Func d) (env : Env d) (o : Operation d)
    (args : HVector toType (sig o.op)) (x : Exit) :
    ExceptT Stuck m (Result (List (DVal d) × Nat)) :=
  match x with
  | .ret =>
    if sig o.op = f.results then pure (.ret (args.toDVals, n))
    else liftExcept (stuck "the function returns values of types other than its result types")
  | .goto i => do
    let (b, env') ← liftExcept (f.jump env o.succs i)
    Func.runOps M n f env' b.body

/-- The spec's computation of the rest of a run of `f` after the op `o`,
which is not a terminator and calls no function, gives `rs`, with the ops
`os` after it and `n` steps left. -/
def afterDenote (M : Module d) (n : Nat) (f : Func d) (env : Env d) (o : Operation d)
    (os : List (Operation d)) (rs : HVector toType (returnTypes o.op)) :
    ExceptT Stuck m (Result (List (DVal d) × Nat)) := do
  let env' ← liftExcept (env.bind (o.results.map (·.1)) rs.toDVals
    "an op names a number of results other than it gives")
  Func.runOps M n f env' os

/-- The spec's computation of the rest of a run of `f` after its call `o`
to the external declaration `@s` gives the values `vs`, with the ops `os`
after it and `n` steps left. -/
def afterExt (M : Module d) (n : Nat) (f : Func d) (env : Env d) (o : Operation d)
    (os : List (Operation d)) (s : Name) (vs : List (DVal d)) :
    ExceptT Stuck m (Result (List (DVal d) × Nat)) :=
  if vs.map (·.1) = returnTypes o.op then do
    let env' ← liftExcept (env.bind (o.results.map (·.1)) vs
      "an op names a number of results other than it gives")
    Func.runOps M n f env' os
  else liftExcept (stuck s!"@{s} gives values of types other than its call's result types")

/-- The spec's computation of the rest of a run of `f` after its call `o`
to `@s` gives `r`, with the ops `os` after it and `n` steps left after the
call's own step. -/
def afterCall (M : Module d) (n : Nat) (f : Func d) (env : Env d) (o : Operation d)
    (os : List (Operation d)) (s : Name) :
    Result (List (DVal d) × Nat) → ExceptT Stuck m (Result (List (DVal d) × Nat))
  | .fuelExhausted => pure .fuelExhausted
  | .ret (vs, k) =>
    if vs.map (·.1) = returnTypes o.op then do
      let env' ← liftExcept (env.bind (o.results.map (·.1)) vs
        "an op names a number of results other than it gives")
      Func.runOps M (min k n) f env' os
    else liftExcept (stuck s!"@{s} returns values of types other than its call's result types")

/-- The spec's computation of a call `o` of `f` to `@s` on the arguments
`cargs`, of the types `ts`, with the ops `os` after it and `n` steps left
for the callee: it enters the function `@s` names, or runs the external-call
rule of the declaration it names, or is stuck. -/
def callAt (M : Module d) (n : Nat) (f : Func d) (env : Env d) (o : Operation d)
    (os : List (Operation d)) (s : Name) {ts : List d.Ty} (cargs : HVector toType ts) :
    ExceptT Stuck m (Result (List (DVal d) × Nat)) :=
  match M.func? s with
  | some g => do
    let (body, genv) ← liftExcept (g.enter cargs.toDVals)
    inFrame (Func.runOps M n g genv body) >>= afterCall M n f env o os s
  | none =>
    if M.declares s ts (returnTypes o.op) then
      ExceptT.lift (DialectExtCall.extCall s cargs.toDVals (returnTypes o.op)) >>=
        afterExt M n f env o os s
    else liftExcept (stuck s!"@{s} is not a function or a declaration of the call's types")

/-- The spec's computation of the rest of a run of `f` after the rule of its
op `o`, on the operands `args`, picks the symbol `@s`, with the ops `os`
after it and `n` steps left after the op's own: with no step left for the
call, the run runs out of fuel; otherwise it calls `@s` on the operands but
the first. -/
def afterPick (M : Module d) (n : Nat) (f : Func d) (env : Env d) (o : Operation d)
    (os : List (Operation d)) (args : HVector toType (sig o.op)) (s : Name) :
    ExceptT Stuck m (Result (List (DVal d) × Nat)) :=
  match n with
  | 0 => pure .fuelExhausted
  | n + 1 => callAt M n f env o os s args.tail

omit [MonadFrame m] in
/-- A check of the interpreter that fails ends the path stuck, whatever
follows it. -/
theorem liftExcept_error_bind [LawfulMonad m] {α β : Type} (e : Stuck)
    (g : α → ExceptT Stuck m β) :
    (liftExcept (.error e) >>= g) = (liftExcept (.error e) : ExceptT Stuck m β) := by
  apply ExceptT.ext
  simp [liftExcept]

/-! # One equation for each case of `Func.runOps` -/

section Equations

variable {M : Module d} {n : Nat} {f : Func d} {env : Env d} {o : Operation d}
  {os : List (Operation d)}

theorem runOps_zero : Func.runOps (m := m) M 0 f env os = pure .fuelExhausted := by
  simp [Func.runOps]

theorem runOps_nil : Func.runOps (m := m) M (n + 1) f env [] =
    liftExcept (stuck "a block ends without a terminator") := by
  simp [Func.runOps]

theorem runOps_region [LawfulMonad m] (h : o.ownsCoreRegion = true) :
    Func.runOps (m := m) M (n + 1) f env (o :: os) =
      liftExcept (stuck "an op owns a region of the core's kind, and no rule runs one") := by
  rw [Func.runOps]
  simp only [h, ite_true, stuck, liftExcept_error_bind]

variable {args : HVector toType (sig o.op)}

theorem runOps_operands [LawfulMonad m] (h : o.ownsCoreRegion = false) {e : Stuck}
    (ha : env.operands (sig o.op) o.operands = .error e) :
    Func.runOps (m := m) M (n + 1) f env (o :: os) = liftExcept (.error e) := by
  rw [Func.runOps]
  simp only [h, ha, Bool.false_eq_true, ↓reduceIte, liftExcept_error_bind]

theorem runOps_follows [LawfulMonad m] (h : o.ownsCoreRegion = false)
    (ha : env.operands (sig o.op) o.operands = .ok args) (hT : isTerminator o.op = true)
    (hos : (!os.isEmpty) = true) :
    Func.runOps (m := m) M (n + 1) f env (o :: os) =
      liftExcept (stuck "an op follows the terminator of its block") := by
  rw [Func.runOps]
  simp only [h, ha, hT, hos, Bool.false_eq_true, ↓reduceIte, liftExcept_ok_bind, stuck,
    liftExcept_error_bind]

theorem runOps_exit [LawfulMonad m] (h : o.ownsCoreRegion = false)
    (ha : env.operands (sig o.op) o.operands = .ok args) (hT : isTerminator o.op = true)
    (hos : (!os.isEmpty) = false) :
    Func.runOps (m := m) M (n + 1) f env (o :: os) =
      ExceptT.lift (DialectDenote.exit o.op args) >>= afterExit M n f env o args := by
  rw [Func.runOps]
  simp only [h, ha, hT, hos, Bool.false_eq_true, ↓reduceIte, liftExcept_ok_bind, stuck]
  rfl

theorem runOps_denote [LawfulMonad m] (h : o.ownsCoreRegion = false)
    (ha : env.operands (sig o.op) o.operands = .ok args) (hT : isTerminator o.op = false)
    (hc : callee? o.op = none) :
    Func.runOps (m := m) M (n + 1) f env (o :: os) =
      ExceptT.lift (DialectDenote.denote o.op args) >>= afterDenote M n f env o os := by
  rw [Func.runOps]
  simp only [h, ha, hT, hc, Bool.false_eq_true, ↓reduceIte, liftExcept_ok_bind]
  rfl

theorem runOps_fixed [LawfulMonad m] (h : o.ownsCoreRegion = false)
    (ha : env.operands (sig o.op) o.operands = .ok args) (hT : isTerminator o.op = false)
    {s : Name} (hc : callee? o.op = some (.fixed s)) :
    Func.runOps (m := m) M (n + 1) f env (o :: os) = callAt M n f env o os s args := by
  rw [Func.runOps]
  simp only [h, ha, hT, hc, Bool.false_eq_true, ↓reduceIte, liftExcept_ok_bind]
  rfl

theorem runOps_pick [LawfulMonad m] (h : o.ownsCoreRegion = false)
    (ha : env.operands (sig o.op) o.operands = .ok args) (hT : isTerminator o.op = false)
    (hc : callee? o.op = some .picked) :
    Func.runOps (m := m) M (n + 1) f env (o :: os) =
      ExceptT.lift (DialectDenote.pick o.op (M.callable (sig o.op).tail (returnTypes o.op)) args) >>=
        afterPick M n f env o os args := by
  rw [Func.runOps]
  simp only [h, ha, hT, hc, Bool.false_eq_true, ↓reduceIte, liftExcept_ok_bind]
  rfl

variable {s : Name} {ts : List d.Ty} {cargs : HVector toType ts}

theorem callAt_noFunc (hg : M.func? s = none) (hd : M.declares s ts (returnTypes o.op) = false) :
    callAt (m := m) M n f env o os s cargs =
      liftExcept (stuck s!"@{s} is not a function or a declaration of the call's types") := by
  simp only [callAt, hg, hd, Bool.false_eq_true, ↓reduceIte]

theorem callAt_ext (hg : M.func? s = none) (hd : M.declares s ts (returnTypes o.op) = true) :
    callAt (m := m) M n f env o os s cargs =
      ExceptT.lift (DialectExtCall.extCall s cargs.toDVals (returnTypes o.op)) >>=
        afterExt M n f env o os s := by
  simp only [callAt, hg, hd, ↓reduceIte]

theorem callAt_enter [LawfulMonad m] {g : Func d} (hg : M.func? s = some g) {e : Stuck}
    (he : g.enter cargs.toDVals = .error e) :
    callAt (m := m) M n f env o os s cargs = liftExcept (.error e) := by
  simp only [callAt, hg, he, liftExcept_error_bind]

theorem callAt_call [LawfulMonad m] {g : Func d} (hg : M.func? s = some g)
    {body : List (Operation d)} {genv : Env d} (he : g.enter cargs.toDVals = .ok (body, genv)) :
    callAt (m := m) M n f env o os s cargs =
      inFrame (Func.runOps M n g genv body) >>= afterCall M n f env o os s := by
  simp only [callAt, hg, he, liftExcept_ok_bind]

end Equations

/-! # A run depends on its environment only through `List.lookup` -/

section Congr

variable (M : Module d)

/-- Runs with `n` steps of fuel do not tell apart environments that give
every name the same value. -/
def RunsSame (n : Nat) : Prop :=
  ∀ (f : Func d) (e₁ e₂ : Env d) (os : List (Operation d)), Same e₁ e₂ →
    Func.runOps (m := m) M n f e₁ os = Func.runOps M n f e₂ os

variable {M} [LawfulMonad m]

theorem afterDenote_congr {n : Nat} (hrun : RunsSame (m := m) M n) (f : Func d) {e₁ e₂ : Env d}
    (h : Same e₁ e₂) (o : Operation d) (os : List (Operation d))
    (rs : HVector toType (returnTypes o.op)) :
    afterDenote (m := m) M n f e₁ o os rs = afterDenote M n f e₂ o os rs := by
  unfold afterDenote
  simp only [bind_eq]
  split
  · rw [liftExcept_ok_bind, liftExcept_ok_bind]
    exact hrun f _ _ os (Same.append _ h)
  · rfl

theorem afterExit_congr {n : Nat} (hrun : RunsSame (m := m) M n) (f : Func d) {e₁ e₂ : Env d}
    (h : Same e₁ e₂) (o : Operation d) (args : HVector toType (sig o.op)) (x : Exit) :
    afterExit (m := m) M n f e₁ o args x = afterExit M n f e₂ o args x := by
  cases x with
  | ret => rfl
  | goto i =>
    dsimp only [afterExit]
    have hj := jump_congr f h o.succs i
    generalize f.jump e₁ o.succs i = r₁ at hj ⊢
    generalize f.jump e₂ o.succs i = r₂ at hj ⊢
    rcases r₁ with e₁' | ⟨b₁, e₁'⟩ <;> rcases r₂ with e₂' | ⟨b₂, e₂'⟩
    · cases hj; rfl
    · exact hj.elim
    · exact hj.elim
    · obtain ⟨rfl, hs⟩ := hj
      rw [liftExcept_ok_bind, liftExcept_ok_bind]
      exact hrun f e₁' e₂' b₁.body hs

theorem afterExt_congr {n : Nat} (hrun : RunsSame (m := m) M n) (f : Func d) {e₁ e₂ : Env d}
    (h : Same e₁ e₂) (o : Operation d) (os : List (Operation d)) (s : Name)
    (vs : List (DVal d)) :
    afterExt (m := m) M n f e₁ o os s vs = afterExt M n f e₂ o os s vs := by
  unfold afterExt
  split
  · simp only [bind_eq]
    split
    · rw [liftExcept_ok_bind, liftExcept_ok_bind]
      exact hrun f _ _ os (Same.append _ h)
    · rfl
  · rfl

theorem afterCall_congr {n : Nat} (hrun : ∀ j ≤ n, RunsSame (m := m) M j) (f : Func d)
    {e₁ e₂ : Env d} (h : Same e₁ e₂) (o : Operation d) (os : List (Operation d)) (s : Name)
    (r : Result (List (DVal d) × Nat)) :
    afterCall (m := m) M n f e₁ o os s r = afterCall M n f e₂ o os s r := by
  cases r with
  | fuelExhausted => rfl
  | ret p =>
    obtain ⟨vs, k⟩ := p
    dsimp only [afterCall]
    split
    · simp only [bind_eq]
      split
      · rw [liftExcept_ok_bind, liftExcept_ok_bind]
        exact hrun _ (Nat.min_le_right k n) f _ _ os (Same.append _ h)
      · rfl
    · rfl

theorem callAt_congr {n : Nat} (hrun : ∀ j ≤ n, RunsSame (m := m) M j) (f : Func d)
    {e₁ e₂ : Env d} (h : Same e₁ e₂) (o : Operation d) (os : List (Operation d)) (s : Name)
    {ts : List d.Ty} (cargs : HVector toType ts) :
    callAt (m := m) M n f e₁ o os s cargs = callAt M n f e₂ o os s cargs := by
  unfold callAt
  split
  · congr 1
    funext p
    obtain ⟨body, genv⟩ := p
    show _ >>= _ = _ >>= _
    congr 1
    funext r
    exact afterCall_congr hrun f h o os s r
  · split
    · congr 1
      funext vs
      exact afterExt_congr (hrun n (Nat.le_refl n)) f h o os s vs
    · rfl

theorem afterPick_congr {n : Nat} (hrun : ∀ j ≤ n, RunsSame (m := m) M j) (f : Func d)
    {e₁ e₂ : Env d} (h : Same e₁ e₂) (o : Operation d) (os : List (Operation d))
    (args : HVector toType (sig o.op)) (s : Name) :
    afterPick (m := m) M n f e₁ o os args s = afterPick M n f e₂ o os args s := by
  match n with
  | 0 => rfl
  | n + 1 =>
    exact callAt_congr (fun j hj => hrun j (Nat.le_succ_of_le hj)) f h o os s args.tail

/-- Two environments that give every name the same value give the same
run. -/
theorem runOps_congr (n : Nat) : RunsSame (m := m) M n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro f e₁ e₂ os h
    match n, os with
    | 0, _ => rw [runOps_zero, runOps_zero]
    | n + 1, [] => rw [runOps_nil, runOps_nil]
    | n + 1, o :: os =>
      have ihn : ∀ j ≤ n, RunsSame (m := m) M j := fun j hj => ih j (Nat.lt_succ_of_le hj)
      by_cases hr : o.ownsCoreRegion = true
      · rw [runOps_region hr, runOps_region hr]
      have hr' := Bool.of_not_eq_true hr
      have hops := operands_congr h (sig o.op) o.operands
      cases ha : e₂.operands (sig o.op) o.operands with
      | error e =>
        rw [runOps_operands hr' (hops.trans ha), runOps_operands hr' ha]
      | ok args =>
        have ha₁ := hops.trans ha
        cases hT : isTerminator o.op with
        | true =>
          cases hos : (!os.isEmpty) with
          | true => rw [runOps_follows hr' ha₁ hT hos, runOps_follows hr' ha hT hos]
          | false =>
            rw [runOps_exit hr' ha₁ hT hos, runOps_exit hr' ha hT hos]
            congr 1
            funext x
            exact afterExit_congr (ihn n (Nat.le_refl n)) f h o args x
        | false =>
          cases hc : callee? o.op with
          | none =>
            rw [runOps_denote hr' ha₁ hT hc, runOps_denote hr' ha hT hc]
            congr 1
            funext rs
            exact afterDenote_congr (ihn n (Nat.le_refl n)) f h o os rs
          | some c =>
            cases c with
            | fixed s =>
              rw [runOps_fixed hr' ha₁ hT hc, runOps_fixed hr' ha hT hc]
              exact callAt_congr ihn f h o os s args
            | picked =>
              rw [runOps_pick hr' ha₁ hT hc, runOps_pick hr' ha hT hc]
              congr 1
              funext s
              exact afterPick_congr ihn f h o os args s

end Congr

end FirRef.Machine
