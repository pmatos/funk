import Fir.Execution.TracePaths

/-!
# The ways a traced step goes on

The run of ops in the traced layer, from a traced state, and the run of a
callee's ops in a call's frame (`Func.traceOps`, `Func.traceCall`); the call
that an op makes, to the callee it names or to the one its rule picks
(`Func.TCallsAt`, #235); and every way in which a path of a run of ops goes
on from its first op (`Func.TStepPath`). `Fir.Execution.TraceStepPaths`
proves that these are the paths of the run.
-/

namespace Fir

open Memory

variable {B α ε : Type}

/-! # The ways a step goes on -/

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

/-- A run in a call's frame, in the traced layer, runs from the traced state
with a new frame entered, and leaves the frame on each path that does not hit
UB. -/
theorem TraceM.run_inFrame (x : ExceptT ε (TraceM B (TraceState Mem unit)) α)
    (s : TraceState Mem unit) (e : TraceEnd B (TraceState Mem unit) (Except ε α)) :
    (inFrame x).run s e ↔ ∃ e', x.run { s with mem := s.mem.enter } e' ∧
      e = e'.map fun r => (r.1, r.2.1, { r.2.2 with mem := r.2.2.mem.exit }) :=
  Iff.rfl

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (TraceM B (TraceState Mem unit))]
  [DialectExtCall d (TraceM B (TraceState Mem unit))]

variable (B) in
/-- The run of ops in the traced layer, from the traced state `s`. -/
abbrev Func.traceOps (M : Module d) (n : Nat) (f : Func d) (env : Env d) (os : List (Operation d))
    (s : TraceState Mem unit) :
    Paths (TraceEnd B (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))) :=
  (Func.runOps (m := TraceM B (TraceState Mem unit)) M n f env os).run s

variable (B) in
/-- The run of a callee's ops in a call's frame in the traced layer, from the
traced state `s`. -/
abbrev Func.traceCall (M : Module d) (n : Nat) (g : Func d) (genv : Env d)
    (body : List (Operation d)) (s : TraceState Mem unit) :
    Paths (TraceEnd B (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))) :=
  (inFrame (Func.runOps (m := TraceM B (TraceState Mem unit)) M n g genv body)).run s

/-- The op `o`, on the operands `args`, from the traced state `s`, with `n`
steps left after its own, calls the symbol `sym` on the arguments `cargs`,
of the types `ts`, with `n'` steps left for the call, from the traced state
`s₁`, after the acts `t₀`: a callee that `o` names, on its operands, from
`s`, with the steps that `o` leaves, after no act; or one that its rule
picks, on its operands but the first, from the traced state the rule ends
with, after the acts it shows and one more step, the call's (#235). -/
inductive Func.TCallsAt (M : Module d) (o : Operation d) (args : HVector toType (sig o.op))
    (s : TraceState Mem unit) :
    Nat → Name → (ts : List d.Ty) → HVector toType ts → Nat → List B → TraceState Mem unit → Prop
  | fixed {n : Nat} {sym : Name} : callee? o.op = some (.fixed sym) →
      Func.TCallsAt M o args s n sym (sig o.op) args n [] s
  | picked {n : Nat} {sym : Name} {t : List B} {s₁ : TraceState Mem unit} :
      callee? o.op = some .picked →
      DialectDenote.pick (m := TraceM B (TraceState Mem unit)) o.op
        (M.callable (sig o.op).tail (returnTypes o.op)) args s (.ok (sym, t, s₁)) →
      Func.TCallsAt M o args s (n + 1) sym (sig o.op).tail args.tail n t s₁


omit [DecidableEq Mem] [DialectExtCall d (TraceM B (TraceState Mem unit))] in
/-- A call leaves its callee at most the steps that its op leaves, and at
least all but one. -/
theorem Func.TCallsAt.le {M : Module d} {o : Operation d} {args : HVector toType (sig o.op)}
    {s s₁ : TraceState Mem unit} {n n' : Nat} {sym : Name} {ts : List d.Ty}
    {cargs : HVector toType ts} {t₀ : List B}
    (h : Func.TCallsAt M o args s n sym ts cargs n' t₀ s₁) : n' ≤ n ∧ n ≤ n' + 1 := by
  cases h with
  | fixed => exact ⟨Nat.le_refl _, Nat.le_succ _⟩
  | picked => exact ⟨Nat.le_succ _, Nat.le_refl _⟩

omit [DecidableEq Mem] [DialectExtCall d (TraceM B (TraceState Mem unit))] in
/-- A call with `j` more steps left after its op leaves its callee `j`
more. -/
theorem Func.TCallsAt.up {M : Module d} {o : Operation d} {args : HVector toType (sig o.op)}
    {s s₁ : TraceState Mem unit} {n n' : Nat} {sym : Name} {ts : List d.Ty}
    {cargs : HVector toType ts} {t₀ : List B} (j : Nat)
    (h : Func.TCallsAt M o args s n sym ts cargs n' t₀ s₁) :
    Func.TCallsAt M o args s (n + j) sym ts cargs (n' + j) t₀ s₁ := by
  cases h with
  | fixed hc => exact .fixed hc
  | picked hc hs => rw [Nat.add_right_comm]; exact .picked hc hs

omit [DecidableEq Mem] [DialectExtCall d (TraceM B (TraceState Mem unit))] in
/-- A call with `j` more steps left after its op makes the same call with
`j` fewer steps left for its callee, unless its callee is picked and its op
leaves no step for the call. -/
theorem Func.TCallsAt.down {M : Module d} {o : Operation d} {args : HVector toType (sig o.op)}
    {s s₁ : TraceState Mem unit} {k j n' : Nat} {sym : Name} {ts : List d.Ty}
    {cargs : HVector toType ts} {t₀ : List B}
    (h : Func.TCallsAt M o args s (k + j) sym ts cargs n' t₀ s₁) :
    (∃ n'', n' = n'' + j ∧ Func.TCallsAt M o args s k sym ts cargs n'' t₀ s₁) ∨
      (k = 0 ∧ callee? o.op = some .picked ∧
        DialectDenote.pick (m := TraceM B (TraceState Mem unit)) o.op
          (M.callable (sig o.op).tail (returnTypes o.op)) args s (.ok (sym, t₀, s₁))) := by
  generalize hm : k + j = m at h
  cases h with
  | fixed hc => exact .inl ⟨k, hm.symm, .fixed hc⟩
  | picked hc hs =>
    cases k with
    | zero => exact .inr ⟨rfl, hc, hs⟩
    | succ k => exact .inl ⟨k, by omega, .picked hc hs⟩

omit [DecidableEq Mem] [DialectExtCall d (TraceM B (TraceState Mem unit))] in
/-- A call at one budget makes the same call at every budget at which its op
leaves the call `m` steps. -/
theorem Func.TCallsAt.at {M : Module d} {o : Operation d} {args : HVector toType (sig o.op)}
    {s s₁ : TraceState Mem unit} {n n' : Nat} {sym : Name} {ts : List d.Ty}
    {cargs : HVector toType ts} {t₀ : List B}
    (h : Func.TCallsAt M o args s n sym ts cargs n' t₀ s₁) (m : Nat) :
    Func.TCallsAt M o args s (m + (n - n')) sym ts cargs m t₀ s₁ := by
  cases h with
  | fixed hc => rw [Nat.sub_self, Nat.add_zero]; exact .fixed hc
  | picked hc hs => rw [show _ + 1 - _ = 1 by omega]; exact .picked hc hs

omit [DecidableEq Mem] [DialectExtCall d (TraceM B (TraceState Mem unit))] in
/-- A call that leaves its callee fewer steps than its op leaves picks its
callee. -/
theorem Func.TCallsAt.picked_of_lt {M : Module d} {o : Operation d}
    {args : HVector toType (sig o.op)} {s s₁ : TraceState Mem unit} {n n' : Nat} {sym : Name}
    {ts : List d.Ty} {cargs : HVector toType ts} {t₀ : List B}
    (h : Func.TCallsAt M o args s n sym ts cargs n' t₀ s₁) (hlt : n' < n) :
    callee? o.op = some .picked ∧
      DialectDenote.pick (m := TraceM B (TraceState Mem unit)) o.op
        (M.callable (sig o.op).tail (returnTypes o.op)) args s (.ok (sym, t₀, s₁)) := by
  cases h with
  | fixed => exact absurd hlt (Nat.lt_irrefl _)
  | picked hc hs => exact ⟨hc, hs⟩

/-- The ways a path of a traced run of the ops `o :: os` of `f`, with `n + 1`
steps, from the traced state `s`, goes on, when it does not end stuck. -/
inductive Func.TStepPath (M : Module d) (n : Nat) (f : Func d) (env : Env d) (o : Operation d)
    (os : List (Operation d)) (s : TraceState Mem unit) :
    TraceEnd B (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat))) → Prop
  | exitUB {args : HVector toType (sig o.op)} {r : String} {t : List B} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = true → os = [] →
      DialectDenote.exit (m := TraceM B (TraceState Mem unit)) o.op args s (.error (r, t)) →
      Func.TStepPath M n f env o os s (.error (r, t))
  | ret {args : HVector toType (sig o.op)} {t : List B} {s' : TraceState Mem unit} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = true → os = [] →
      DialectDenote.exit (m := TraceM B (TraceState Mem unit)) o.op args s (.ok (.ret, t, s')) →
      sig o.op = f.results →
      Func.TStepPath M n f env o os s (.ok (.ok (.ret (args.toDVals, n)), t, s'))
  | goto {args : HVector toType (sig o.op)} {i : Nat} {t : List B} {s' : TraceState Mem unit}
      {b : Block d} {env₁ : Env d} {e} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = true → os = [] →
      DialectDenote.exit (m := TraceM B (TraceState Mem unit)) o.op args s (.ok (.goto i, t, s')) →
      f.jump env o.succs i = .ok (b, env₁) → Func.traceOps B M n f env₁ b.body s' e →
      Func.TStepPath M n f env o os s (e.after t)
  | denoteUB {args : HVector toType (sig o.op)} {r : String} {t : List B} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = none →
      DialectDenote.denote (m := TraceM B (TraceState Mem unit)) o.op args s (.error (r, t)) →
      Func.TStepPath M n f env o os s (.error (r, t))
  | denote {args : HVector toType (sig o.op)} {rs : HVector toType (returnTypes o.op)} {t : List B}
      {s' : TraceState Mem unit} {e} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = none →
      DialectDenote.denote (m := TraceM B (TraceState Mem unit)) o.op args s (.ok (rs, t, s')) →
      (o.results.map (·.1)).length = rs.toDVals.length →
      Func.traceOps B M n f ((o.results.map (·.1)).zip rs.toDVals ++ env) os s' e →
      Func.TStepPath M n f env o os s (e.after t)
  | callUB {args : HVector toType (sig o.op)} {sym : Name} {ts : List d.Ty}
      {cargs : HVector toType ts} {n' : Nat} {t₀ : List B} {s₁ : TraceState Mem unit} {g : Func d}
      {body genv} {r : String} {t : List B} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → Func.TCallsAt M o args s n sym ts cargs n' t₀ s₁ →
      M.func? sym = some g → g.enter cargs.toDVals = .ok (body, genv) →
      Func.traceCall B M n' g genv body s₁ (.error (r, t)) →
      Func.TStepPath M n f env o os s (TraceEnd.after t₀ (.error (r, t)))
  | callExh {args : HVector toType (sig o.op)} {sym : Name} {ts : List d.Ty}
      {cargs : HVector toType ts} {n' : Nat} {t₀ : List B} {s₁ : TraceState Mem unit} {g : Func d}
      {body genv} {t : List B} {s' : TraceState Mem unit} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → Func.TCallsAt M o args s n sym ts cargs n' t₀ s₁ →
      M.func? sym = some g → g.enter cargs.toDVals = .ok (body, genv) →
      Func.traceCall B M n' g genv body s₁ (.ok (.ok .fuelExhausted, t, s')) →
      Func.TStepPath M n f env o os s (TraceEnd.after t₀ (.ok (.ok .fuelExhausted, t, s')))
  | callRet {args : HVector toType (sig o.op)} {sym : Name} {ts : List d.Ty}
      {cargs : HVector toType ts} {n' : Nat} {t₀ : List B} {s₁ : TraceState Mem unit} {g : Func d}
      {body genv} {vs : List (DVal d)} {k : Nat} {t : List B} {s' : TraceState Mem unit} {e} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → Func.TCallsAt M o args s n sym ts cargs n' t₀ s₁ →
      M.func? sym = some g → g.enter cargs.toDVals = .ok (body, genv) →
      Func.traceCall B M n' g genv body s₁ (.ok (.ok (.ret (vs, k)), t, s')) →
      vs.map (·.1) = returnTypes o.op → (o.results.map (·.1)).length = vs.length →
      Func.traceOps B M (min k n') f ((o.results.map (·.1)).zip vs ++ env) os s' e →
      Func.TStepPath M n f env o os s ((e.after t).after t₀)
  | extUB {args : HVector toType (sig o.op)} {sym : Name} {ts : List d.Ty}
      {cargs : HVector toType ts} {n' : Nat} {t₀ : List B} {s₁ : TraceState Mem unit} {r : String}
      {t : List B} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → Func.TCallsAt M o args s n sym ts cargs n' t₀ s₁ →
      M.func? sym = none → M.declares sym ts (returnTypes o.op) = true →
      DialectExtCall.extCall (m := TraceM B (TraceState Mem unit)) sym cargs.toDVals
        (returnTypes o.op) s₁ (.error (r, t)) →
      Func.TStepPath M n f env o os s (TraceEnd.after t₀ (.error (r, t)))
  | ext {args : HVector toType (sig o.op)} {sym : Name} {ts : List d.Ty}
      {cargs : HVector toType ts} {n' : Nat} {t₀ : List B} {s₁ : TraceState Mem unit} {vs : List (DVal d)}
      {t : List B} {s' : TraceState Mem unit} {e} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → Func.TCallsAt M o args s n sym ts cargs n' t₀ s₁ →
      M.func? sym = none → M.declares sym ts (returnTypes o.op) = true →
      DialectExtCall.extCall (m := TraceM B (TraceState Mem unit)) sym cargs.toDVals
        (returnTypes o.op) s₁ (.ok (vs, t, s')) →
      vs.map (·.1) = returnTypes o.op → (o.results.map (·.1)).length = vs.length →
      Func.traceOps B M n' f ((o.results.map (·.1)).zip vs ++ env) os s' e →
      Func.TStepPath M n f env o os s ((e.after t).after t₀)
  | pickUB {args : HVector toType (sig o.op)} {r : String} {t : List B} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = some .picked →
      DialectDenote.pick (m := TraceM B (TraceState Mem unit)) o.op
        (M.callable (sig o.op).tail (returnTypes o.op)) args s (.error (r, t)) →
      Func.TStepPath M n f env o os s (.error (r, t))
  | pickExh {args : HVector toType (sig o.op)} {sym : Name} {t : List B}
      {s₁ : TraceState Mem unit} :
      o.ownsCoreRegion = false → env.operands (sig o.op) o.operands = .ok args →
      isTerminator o.op = false → callee? o.op = some .picked →
      DialectDenote.pick (m := TraceM B (TraceState Mem unit)) o.op
        (M.callable (sig o.op).tail (returnTypes o.op)) args s (.ok (sym, t, s₁)) → n = 0 →
      Func.TStepPath M n f env o os s (.ok (.ok .fuelExhausted, t, s₁))

/-- A traced run with no fuel runs out of fuel, showing nothing, and only
so. -/
theorem Func.traceOps_zero {M : Module d} {f : Func d} {env : Env d} {os : List (Operation d)}
    {s : TraceState Mem unit}
    {e : TraceEnd B (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))} :
    Func.traceOps B M 0 f env os s e ↔ e = .ok (.ok .fuelExhausted, [], s) := by
  simp only [Func.traceOps, Func.runOps]
  exact Iff.rfl

/-- A block with no op left is stuck, from any traced state. -/
theorem Func.traceOps_nil {M : Module d} {n : Nat} {f : Func d} {env : Env d}
    {s : TraceState Mem unit}
    {e : TraceEnd B (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))}
    (hne : TraceEnd.NotStuck e) : ¬ Func.traceOps B M (n + 1) f env [] s e := by
  simp only [Func.traceOps, Func.runOps]
  exact TraceM.run_stuck hne

end Fir
