import Fir.Execution.TraceStepPaths

/-!
# The call of a target that refines a source's, in the traced layer

A call of the target, on operands that refine the source's and from a
traced state that refines the source's, is a call of the source too: to the
same symbol, with the same steps left for the callee, on arguments that the
target's refine, after acts that the target's refine one by one, from a
traced state that the target's refines. The callee that an op names is the
same in both. The rule that picks a callee (#235), when it is monotone and
the target can call each symbol that the source can, picks the same symbol
in the source after acts that the target's refine, or hits UB after acts
that the target's first show, refined.
-/

namespace Fir

open Memory

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem] {B : Type} [HRefinement B B]
  {d : Dialect} [TyDenote d.Ty] [TyRefinement d.Ty]

variable [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (TraceM B (TraceState Mem unit))]
  [DialectExtCall d (TraceM B (TraceState Mem unit))]

omit [DialectExtCall d (TraceM B (TraceState Mem unit))] in
/-- A call of the target, on operands that refine the source's, from a
traced state that refines the source's, is a call of the source to the same
symbol on arguments that the target's refine, after acts that the target's
refine one by one, from a traced state that the target's refines; or the
source's rule that picks the callee hits UB after acts that the target's
first show, refined. It asks that the rule be monotone, and that the target
can call each symbol that the source can. -/
theorem Func.TCallsAt.source {M M' : Module d} {o : Operation d}
    {args args' : HVector toType (sig o.op)} (hr : args.Forall₂ TyRefinement.IsRefinedBy args')
    {s s' : TraceState Mem unit} (hS : s ⊑ s')
    (hok : ∀ ts rs x, M.callable ts rs x = true → M'.callable ts rs x = true)
    (hpm : callee? o.op = some .picked →
      OpTracePickMonotone (B := B) (σ := TraceState Mem unit) o.op)
    {n n' : Nat} {sym : Name} {ts : List d.Ty} {cargs' : HVector toType ts} {t₀' : List B}
    {s₁' : TraceState Mem unit} (h : Func.TCallsAt M' o args' s' n sym ts cargs' n' t₀' s₁') :
    (∃ (cargs : HVector toType ts) (t₀ : List B) (s₁ : TraceState Mem unit),
      Func.TCallsAt M o args s n sym ts cargs n' t₀ s₁ ∧
        cargs.Forall₂ TyRefinement.IsRefinedBy cargs' ∧ t₀ ⊑ t₀' ∧ s₁ ⊑ s₁') ∨
    (callee? o.op = some .picked ∧ ∃ (r : String) (t : List B),
      DialectDenote.pick (m := TraceM B (TraceState Mem unit)) o.op
        (M.callable (sig o.op).tail (returnTypes o.op)) args s (.error (r, t)) ∧
      List.IsRefinedPrefix t t₀') := by
  cases h with
  | fixed hc => exact .inl ⟨args, [], s, .fixed hc, hr, trivial, hS⟩
  | picked hc hs =>
    obtain ⟨e, he, hle⟩ := hpm hc _ _ (hok _ _) args args' hr s s' hS _ hs
    match e, he, hle with
    | .ok (_, t₀, s₁), he, ⟨rfl, ht, hs₁⟩ =>
      exact .inl ⟨args.tail, t₀, s₁, .picked hc he, hr.tail, ht, hs₁⟩
    | .error (r, t), he, hle => exact .inr ⟨hc, r, t, he, hle⟩

/-- The external-call rule for the symbol that an op calls, on the types of
its arguments, is monotone when it is for each callee that the op names, and
for each symbol on its operands but the first when its callee is picked. -/
theorem Func.TCallsAt.extMonotone {M : Module d} {o : Operation d}
    {args : HVector toType (sig o.op)} {s : TraceState Mem unit} {n n' : Nat} {sym : Name}
    {ts : List d.Ty} {cargs : HVector toType ts} {t₀ : List B} {s₁ : TraceState Mem unit}
    (h : Func.TCallsAt M o args s n sym ts cargs n' t₀ s₁) (hT : isTerminator o.op = false)
    (hops : TraceMonotoneOps B (TraceState Mem unit) [o]) :
    ExtTraceMonotone (B := B) (σ := TraceState Mem unit) sym ts (returnTypes o.op) := by
  cases h with
  | fixed hc => exact (hops o List.mem_cons_self).2.1 hT _ hc
  | picked hc => exact ((hops o List.mem_cons_self).2.2 hT hc).2 sym

end Fir
