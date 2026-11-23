import Fir.Execution.Monotone
import Fir.Execution.Propagation

/-!
# The callee of a call

An op calls a function in one of two ways (#235): it names its callee, as
`call @g` names `@g`, or its rule picks the callee when it runs, as a call
through a pointer does. Either way the run then calls one symbol on some
arguments, with the steps the call leaves, exactly as it calls a named
callee: it runs the function of the module with that symbol, or the
external-call rule when the symbol names a declaration. This section names
that symbol and those arguments once, so that the proofs that follow a run
step by step treat both kinds of call as one:

* an op that names its callee calls it on its operands, of its operand
  types, with the steps that the op leaves;
* an op whose callee is picked calls the symbol that its rule picks on its
  operands but the first, which is what the rule picks from, of their
  types, after one more step: its rule takes the op's step, and the call
  one of its own. With no step left for the call, the run runs out of fuel
  there.

When the operands of an op that picks its callee refine others, and the
target module can call each symbol that the source can, a monotone rule
picks, on the target's operands, a symbol that it picks on the source's, or
is UB on the source's: so the source calls the same symbol on arguments
that the target's refine.
-/

namespace Fir

open SetM

/-- The budget of a call's callee in the target is large enough for the
source's callee: a call whose op leaves the target `bound + 1` times the
source's steps, plus `bound`, and leaves its callee all of them or all but
one, leaves its callee so too. -/
theorem callee_budget {bound N₀ n n' : Nat} (h : n' ≤ n ∧ n ≤ n' + 1) (hle : n - n' ≤ N₀)
    (hb : bound + (bound + 1) * (N₀ + 1) ≤ n) :
    bound + (bound + 1) * (N₀ - (n - n') + 1) ≤ n' := by
  rcases Nat.lt_or_ge n' n with hlt | hfit
  · rw [show N₀ - (n - n') + 1 = N₀ by omega]
    rw [Nat.mul_succ] at hb
    omega
  · rw [show n - n' = 0 by omega, Nat.sub_zero]
    omega

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d SetM]

/-- The op `o`, on the operands `args`, with `n` steps left after its own,
calls the symbol `s` on the arguments `cargs`, of the types `ts`, with `n'`
steps left for the call: a callee that `o` names, on its operands, with the
steps that `o` leaves; or one that its rule picks, on its operands but the
first, after one more step, the call's (#235). -/
inductive Func.CallsAt (M : Module d) (o : Operation d) (args : HVector toType (sig o.op)) :
    Nat → Name → (ts : List d.Ty) → HVector toType ts → Nat → Prop
  | fixed {n : Nat} {s : Name} : callee? o.op = some (.fixed s) →
      Func.CallsAt M o args n s (sig o.op) args n
  | picked {n : Nat} {s : Name} : callee? o.op = some .picked →
      DialectDenote.pick (m := SetM) o.op (M.callable (sig o.op).tail (returnTypes o.op)) args
        (.ok s) →
      Func.CallsAt M o args (n + 1) s (sig o.op).tail args.tail n

variable {M : Module d} {o : Operation d} {args : HVector toType (sig o.op)} {n n' : Nat}
  {s : Name} {ts : List d.Ty} {cargs : HVector toType ts}

/-- A call leaves its callee at most the steps that its op leaves, and at
least all but one. -/
theorem Func.CallsAt.le (h : Func.CallsAt M o args n s ts cargs n') : n' ≤ n ∧ n ≤ n' + 1 := by
  cases h with
  | fixed _ => exact ⟨Nat.le_refl _, Nat.le_succ _⟩
  | picked _ _ => exact ⟨Nat.le_succ _, Nat.le_refl _⟩

/-- A call with `j` more steps left after its op leaves its callee `j` more. -/
theorem Func.CallsAt.up (j : Nat) (h : Func.CallsAt M o args n s ts cargs n') :
    Func.CallsAt M o args (n + j) s ts cargs (n' + j) := by
  cases h with
  | fixed hc => exact .fixed hc
  | picked hc hs => rw [Nat.add_right_comm]; exact .picked hc hs

/-- A call with `j` more steps left after its op calls the same symbol on
the same arguments with `j` fewer steps left for its callee, unless its
callee is picked and its op leaves no step for the call. -/
theorem Func.CallsAt.down {k j : Nat} (h : Func.CallsAt M o args (k + j) s ts cargs n') :
    (∃ n'', n' = n'' + j ∧ Func.CallsAt M o args k s ts cargs n'') ∨
      (k = 0 ∧ callee? o.op = some .picked ∧
        DialectDenote.pick (m := SetM) o.op (M.callable (sig o.op).tail (returnTypes o.op)) args
          (.ok s)) := by
  generalize hm : k + j = m at h
  cases h with
  | fixed hc => exact .inl ⟨k, hm.symm, .fixed hc⟩
  | picked hc hs =>
    cases k with
    | zero => exact .inr ⟨rfl, hc, hs⟩
    | succ k => exact .inl ⟨k, by omega, .picked hc hs⟩

/-- A call at one budget calls the same symbol on the same arguments at
every budget at which its op leaves the call `m` steps. -/
theorem Func.CallsAt.at (h : Func.CallsAt M o args n s ts cargs n') (m : Nat) :
    Func.CallsAt M o args (m + (n - n')) s ts cargs m := by
  cases h with
  | fixed hc => rw [Nat.sub_self, Nat.add_zero]; exact .fixed hc
  | picked hc hs => rw [show _ + 1 - _ = 1 by omega]; exact .picked hc hs

/-- A call that leaves its callee fewer steps than its op leaves picks its
callee. -/
theorem Func.CallsAt.picked_of_lt (h : Func.CallsAt M o args n s ts cargs n') (hlt : n' < n) :
    callee? o.op = some .picked ∧
      DialectDenote.pick (m := SetM) o.op (M.callable (sig o.op).tail (returnTypes o.op)) args
        (.ok s) := by
  cases h with
  | fixed _ => exact absurd hlt (Nat.lt_irrefl _)
  | picked hc hs => exact ⟨hc, hs⟩

variable [TyRefinement d.Ty]

/-- A call of the target, on operands that refine the source's, is a call
of the source to the same symbol, with the same steps, on arguments that the
target's refine; or the source's rule that picks the callee hits UB. It
asks that the rule be monotone, and that the target can call each symbol
that the source can. -/
theorem Func.CallsAt.source {M M' : Module d} {o : Operation d}
    {args args' : HVector toType (sig o.op)} (hr : args.Forall₂ TyRefinement.IsRefinedBy args')
    (hok : ∀ ts rs s, M.callable ts rs s = true → M'.callable ts rs s = true)
    (hpm : callee? o.op = some .picked → PickMonotone o.op)
    {n n' : Nat} {s : Name} {ts : List d.Ty} {cargs' : HVector toType ts}
    (h : Func.CallsAt M' o args' n s ts cargs' n') :
    (∃ cargs : HVector toType ts, Func.CallsAt M o args n s ts cargs n' ∧
      cargs.Forall₂ TyRefinement.IsRefinedBy cargs') ∨
    (callee? o.op = some .picked ∧ ∃ r, DialectDenote.pick (m := SetM) o.op
      (M.callable (sig o.op).tail (returnTypes o.op)) args (.ub r)) := by
  cases h with
  | fixed hc => exact .inl ⟨args, .fixed hc, hr⟩
  | picked hc hs =>
    obtain ⟨e, he, hle⟩ := hpm hc _ _ (hok _ _) args args' hr _ hs
    match e, he, hle with
    | .ok _, he, rfl => exact .inl ⟨args.tail, .picked hc he, hr.tail⟩
    | .ub r, he, _ => exact .inr ⟨hc, r, he⟩

end Fir
