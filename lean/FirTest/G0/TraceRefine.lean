import Fir
import FirRef

/-!
G0's check on the Lean side, for refinement over traced runs (ADR-2026-11-03-0600,
`docs/decisions/semantics-m1-trace-refinement.md`), split from `FirTest.G0` by subject.
Each statement below is made of an arbitrary dialect `d`, or an arbitrary
base and extension, with the spec's own proof, so it builds only while those
stay parameterized over the dialect. `scripts/check_g0.py` checks this file
as it checks the other files of `FirTest/G0/`.

They restate, over traced runs, for every dialect whose ops show no event,
the refinement results: refined arguments, and congruence in the callee
with a budget for the new callee or, when the dialect's ops have finitely
many outcomes, with none, each from what holds with memory; that a
dialect's semantics with memory, lifted, is a traced semantics that lifts
it; and that a sum's values hold pointers when both sides' do. A dialect
whose ops show events needs the theorems of the traced layer itself, which
stages 3b and 3c of #233 give: the last section restates those of stage 3b,
for returns, UB, each budget and divergence, under the human's ruling of
2026-11-20 that each op has finitely many outcomes given the world's
answers; that a dialect with no event meets their obligation and that
hypothesis; and that every module bounds its chains of calls.
-/

namespace FirTest.G0

open Fir Fir.Memory

/-! # A dialect with no event -/

/-- Every dialect's semantics with memory, lifted onto the memories of the
traced state, is a traced semantics that lifts it. -/
theorem ofMem_liftsMem (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
    [DialectCall d] [DialectEffects d] [DialectMemDenote d] :
    @LiftsMem d _ _ _ _ _ _ (DialectTrace.ofMem d) :=
  DialectTrace.ofMem_liftsMem d

/-- The values of every sum hold pointers when both sides' do. -/
example (base e : Dialect) [TyDenote base.Ty] [TyDenote e.Ty] [TyRefinement base.Ty]
    [TyRefinement e.Ty] [TyPointers base.Ty] [TyPointers e.Ty] : TyPointers (base ⊞ e).Ty :=
  inferInstance

/-! # Refinement over traced runs -/

/-- For every function of every dialect whose ops show no event, when its
runs from the memories a run starts with refine another's, the memories
they end with included, its traced runs refine the other's. -/
theorem traceRuns_isRefinedBy_of_from (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectCall d] [DialectEffects d] [DialectMemDenote d]
    [TyRefinement d.Ty] [TyPointers d.Ty] [DialectTrace d] [LiftsMem d] {N : Type}
    [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) (L : RunItems)
    (μ : Nat → N) (ar : AddrRule)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    {M M' : Module d} {f f' : Func d} {a : HVector toType (f.params.map (·.2))}
    {a' : HVector toType (f'.params.map (·.2))}
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ L
      observable (f.memRunsFrom M (a, (RunItems.start d lay ρ L))) ⊑
        observable (f'.memRunsFrom M' (a', (RunItems.start d lay ρ L)))) :
    traceObservable (f.traceRuns lay ρ L μ ar M a) ⊑
      traceObservable (f'.traceRuns lay ρ L μ ar M' a') :=
  Func.traceRuns_isRefinedBy_of_from lay ρ L μ ar htrans h

/-- Refined arguments over traced runs, for every function of a module whose
functions are valid, of every dialect lawful in its monotonicity whose ops
show no event, wherever a run names its memories, at every world. -/
theorem traceRuns_args_isRefinedBy (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectCall d] [DialectEffects d] [DialectMemDenote d]
    [DialectValidation d] [TyRefinement d.Ty] [TyPointers d.Ty] [LawfulDialectMonotone d]
    [DialectTrace d] [LiftsMem d] [Inhabited (DialectTrace.Answer d)] {N : Type}
    [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) (L : RunItems)
    (μ : Nat → N) (ar : AddrRule)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    {ctx : ModuleContext d} {M : Module d} (hv : ∀ g ∈ M.funcs, g.Valid ctx) {f : Func d}
    (hf : f ∈ M.funcs) {a a' : HVector toType (f.params.map (·.2))}
    (ha : a.Forall₂ TyRefinement.IsRefinedBy a') :
    ∀ w t, (traceObservable (f.traceRuns lay ρ L μ ar M a')).atWorld w t →
      ∃ s, traceObservable (f.traceRuns lay ρ L μ ar M a) s ∧ s ⊑ t :=
  TBehaviour.isRefinedBy_iff_world.1
    (Func.traceRuns_args_isRefinedBy_of_lawful lay ρ L μ ar htrans hv hf ha)

/-- Congruence in the callee over traced runs, for every function of a valid
module of every dialect lawful in its monotonicity whose ops show no event,
wherever a run names its memories, when the new body, run from given
memories, refines the old one and has one budget past which it runs out of
fuel only if it diverges. -/
theorem traceRuns_replaceBody_isRefinedBy (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectCall d] [DialectEffects d] [DialectMemDenote d]
    [DialectValidation d] [TyRefinement d.Ty] [TyPointers d.Ty] [LawfulDialectMonotone d]
    [DialectTrace d] [LiftsMem d] {N : Type} [DecidableEq N] (lay : N → MemLayout)
    (ρ : DialectEffects.Mem d → N) (L : RunItems) (μ : Nat → N) (ar : AddrRule)
    (hrefl : ∀ {t : d.Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    {M : Module d} (hM : M.Valid) {g : Func d} (hg : g ∈ M.funcs) (b : Region d)
    (hbound : letI := DialectMemDenote.denoteAt (d := d) lay ρ L
      ∃ B, ((g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay)
        (M.replaceBody g.name b)).BoundedBy B)
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ L;
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) M ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay) (M.replaceBody
            g.name b))
    {f : Func d} (hf : f ∈ M.funcs) :
    f.traceRuns lay ρ L μ ar M ⊑
      (f.replaceBody g.name b).traceRuns lay ρ L μ ar (M.replaceBody g.name b) :=
  Func.traceRuns_replaceBody_isRefinedBy_of_bound lay ρ L μ ar hrefl htrans hM hg b hbound h hf

/-- Congruence in the callee over traced runs, with no budget, for every
function of a valid module of every dialect lawful in its monotonicity whose
ops show no event and have finitely many outcomes, wherever a run names its
memories, when the new body, run from given memories, refines the old one,
at every world. -/
theorem traceRuns_replaceBody_isRefinedBy_of_opsFinite (d : Dialect) [TyDenote d.Ty]
    [DecidableEq d.Ty] [DialectSignature d] [DialectCall d] [DialectEffects d] [DialectMemDenote d]
    [DialectValidation d] [TyRefinement d.Ty] [TyPointers d.Ty] [LawfulDialectMonotone d]
    [DialectTrace d] [LiftsMem d] [Inhabited (DialectTrace.Answer d)] {N : Type}
    [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) (L : RunItems)
    (μ : Nat → N) (ar : AddrRule)
    (hrefl : ∀ {t : d.Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    (hfin : letI := DialectMemDenote.denoteAt (d := d) lay ρ L; OpsFinite d N (unitsOf lay))
    {M : Module d} (hM : M.Valid) {g : Func d} (hg : g ∈ M.funcs) (b : Region d)
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ L;
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) M ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay) (M.replaceBody
            g.name b))
    {f : Func d} (hf : f ∈ M.funcs) :
    ∀ a w t, (traceObservable ((f.replaceBody g.name b).traceRuns lay ρ L μ ar
        (M.replaceBody g.name b) a)).atWorld w t →
      ∃ s, traceObservable (f.traceRuns lay ρ L μ ar M a) s ∧ s ⊑ t :=
  FuncTraceRuns.isRefinedBy_iff_world.1
    (Func.traceRuns_replaceBody_isRefinedBy_of_opsFinite lay ρ L μ ar hrefl htrans hfin hM hg b h
      hf)

/-! # A dialect with events -/

/-- Refined arguments over traced runs, for each return, for every function
of a module of every dialect, events included, whose terminators and ops
with no callee are monotone in the traced layer, wherever a run names its
memories. -/
theorem traceRuns_ret_allowed (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectCall d] [DialectEffects d] [DialectTrace d] [TyRefinement d.Ty]
    [TyPointers d.Ty] {N : Type} [DecidableEq N] (lay : N → MemLayout)
    (ρ : DialectEffects.Mem d → N) (L : RunItems) (μ : Nat → N) (ar : AddrRule)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    {M : Module d} {f : Func d}
    (hmono : letI := DialectTrace.traceAt (d := d) lay ρ L
      ∀ g ∈ M.funcs, g.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (hf : letI := DialectTrace.traceAt (d := d) lay ρ L
      f.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    {a a' : HVector toType (f.params.map (·.2))} (ha : a.Forall₂ TyRefinement.IsRefinedBy a')
    {tr : List (DialectTrace.Acts d)} {o' : End (unitsOf lay) μ ar (List (DVal d))}
    (h : traceObservable (f.traceRuns lay ρ L μ ar M a') (.ret tr o')) :
    ∃ s : TOutcome (DialectTrace.Acts d) (End (unitsOf lay) μ ar (List (DVal d))),
      traceObservable (f.traceRuns lay ρ L μ ar M a) s ∧
        s ⊑ (.ret tr o' : TOutcome (DialectTrace.Acts d) (End (unitsOf lay) μ ar (List (DVal d)))) :=
  Func.traceRuns_ret_allowed lay ρ L μ ar htrans hmono hf ha h

/-- Refined arguments over traced runs, for each UB, for every function of a
module of every dialect, events included, whose terminators and ops with no
callee are monotone in the traced layer, wherever a run names its
memories. -/
theorem traceRuns_ub_allowed (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectCall d] [DialectEffects d] [DialectTrace d] [TyRefinement d.Ty]
    [TyPointers d.Ty] {N : Type} [DecidableEq N] (lay : N → MemLayout)
    (ρ : DialectEffects.Mem d → N) (L : RunItems) (μ : Nat → N) (ar : AddrRule)
    {M : Module d} {f : Func d}
    (hmono : letI := DialectTrace.traceAt (d := d) lay ρ L
      ∀ g ∈ M.funcs, g.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (hf : letI := DialectTrace.traceAt (d := d) lay ρ L
      f.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    {a a' : HVector toType (f.params.map (·.2))} (ha : a.Forall₂ TyRefinement.IsRefinedBy a')
    {tr : List (DialectTrace.Acts d)} {r' : String}
    (h : traceObservable (f.traceRuns lay ρ L μ ar M a') (.ub tr r')) :
    ∃ s : TOutcome (DialectTrace.Acts d) (End (unitsOf lay) μ ar (List (DVal d))),
      traceObservable (f.traceRuns lay ρ L μ ar M a) s ∧
        s ⊑ (.ub tr r' : TOutcome (DialectTrace.Acts d) (End (unitsOf lay) μ ar (List (DVal d)))) :=
  Func.traceRuns_ub_allowed lay ρ L μ ar hmono hf ha h

/-- Refined arguments over traced runs, at each budget, for each path that
runs out of fuel, for every function of a module of every dialect, events
included, whose terminators and ops with no callee are monotone in the
traced layer. -/
theorem traceRuns_exhausted_allowed (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectCall d] [DialectEffects d] [DialectTrace d] [TyRefinement d.Ty]
    {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N)
    (L : RunItems) (μ : Nat → N) (ar : AddrRule) {M : Module d} {f : Func d}
    (hmono : letI := DialectTrace.traceAt (d := d) lay ρ L
      ∀ g ∈ M.funcs, g.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (hf : letI := DialectTrace.traceAt (d := d) lay ρ L
      f.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    {a a' : HVector toType (f.params.map (·.2))} (ha : a.Forall₂ TyRefinement.IsRefinedBy a')
    {n : Nat} {mt' : List (Step (DialectTrace.Acts d))}
    (hx : f.traceRuns lay ρ L μ ar M a' n (.ok (.ok .fuelExhausted, mt'))) :
    (∃ mt, f.traceRuns lay ρ L μ ar M a n (.ok (.ok .fuelExhausted, mt)) ∧ mt ⊑ mt') ∨
      ∃ r mt, f.traceRuns lay ρ L μ ar M a n (.error (r, mt)) ∧ List.IsRefinedPrefix mt mt' :=
  Func.traceRuns_exhausted_allowed lay ρ L μ ar hmono hf ha hx

/-- Every dialect whose ops show no event meets the obligation of the traced
layer for every function whose ops are monotone with memory. -/
theorem traceOpsMonotone_ofMem (d : Dialect) [TyDenote d.Ty] [DialectSignature d]
    [DialectCall d] [DialectEffects d] [DialectMemDenote d] [TyRefinement d.Ty] {N : Type}
    [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) (L : RunItems)
    {f : Func d}
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ L; f.MemOpsMonotone N (unitsOf lay)) :
    letI := DialectTrace.ofMem d
    letI := DialectTrace.traceAt (d := d) lay ρ L
    f.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)) :=
  Func.TraceOpsMonotone.ofMem lay ρ L h

/-- Every dialect whose ops show no event has ops of finitely many outcomes in
the traced layer, given the world's answers, when they have finitely many
with memory. -/
theorem opsTraceFinite_ofMem (d : Dialect) [TyDenote d.Ty] [DialectSignature d]
    [DialectCall d] [DialectEffects d] [DialectMemDenote d] {N : Type} [DecidableEq N]
    (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) (L : RunItems)
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ L; OpsFinite d N (unitsOf lay)) :
    letI := DialectTrace.ofMem d
    letI := DialectTrace.traceAt (d := d) lay ρ L
    OpsTraceFinite d (DialectTrace.Event d) (DialectTrace.Answer d) (TraceState N (unitsOf lay)) :=
  OpsTraceFinite.ofMem lay ρ L h

/-- Every dialect whose ops each lift their rule with memory, and whose
external-call rule lifts its rule with memory, meets the obligation of the
traced layer for every function whose ops are monotone with memory. -/
theorem traceOpsMonotone_ofLift (d : Dialect) [TyDenote d.Ty] [DialectSignature d]
    [DialectCall d] [DialectEffects d] [DialectMemDenote d] [DialectTrace d] [TyRefinement d.Ty]
    {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N)
    (L : RunItems) {f : Func d} (hl : ∀ op : d.Op, OpLiftsMem lay ρ L op)
    (hlx : letI := DialectTrace.traceAt (d := d) lay ρ L
      (MonadMorphism.traceMem N (unitsOf lay) (DialectTrace.Acts d)).MapsExtCall (d := d))
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ L; f.MemOpsMonotone N (unitsOf lay)) :
    letI := DialectTrace.traceAt (d := d) lay ρ L
    f.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)) :=
  Func.TraceOpsMonotone.ofLift lay ρ L hl hlx h

/-- Every dialect whose ops each lift their rule with memory, and whose
external-call rule lifts its rule with memory, has ops of finitely many
outcomes in the traced layer, given the world's answers, when they have
finitely many with memory. -/
theorem opsTraceFinite_ofLift (d : Dialect) [TyDenote d.Ty] [DialectSignature d]
    [DialectCall d] [DialectEffects d] [DialectMemDenote d] [DialectTrace d] {N : Type}
    [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) (L : RunItems)
    (hl : ∀ op : d.Op, OpLiftsMem lay ρ L op)
    (hlx : letI := DialectTrace.traceAt (d := d) lay ρ L
      (MonadMorphism.traceMem N (unitsOf lay) (DialectTrace.Acts d)).MapsExtCall (d := d))
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ L; OpsFinite d N (unitsOf lay)) :
    letI := DialectTrace.traceAt (d := d) lay ρ L
    OpsTraceFinite d (DialectTrace.Event d) (DialectTrace.Answer d) (TraceState N (unitsOf lay)) :=
  OpsTraceFinite.ofLift lay ρ L hl hlx h

/-- Every module of every dialect bounds its chains of calls: some `W`
exceeds the length of each by at least one. -/
theorem exists_callBound (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
    [DialectCall d] (M : Module d) : ∃ W, 0 < W ∧ ∀ os c, M.CallChain os c → c + 1 ≤ W :=
  M.exists_callBound

/-- Refined arguments over traced runs, divergence included, for every
function of a module of every dialect, events included, whose terminators
and ops with no callee are monotone in the traced layer and whose ops have
finitely many outcomes given the world's answers, wherever a run names its
memories. -/
theorem traceRuns_isRefinedBy_of_args (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectCall d] [DialectEffects d] [DialectTrace d] [TyRefinement d.Ty]
    [TyPointers d.Ty] {N : Type} [DecidableEq N] (lay : N → MemLayout)
    (ρ : DialectEffects.Mem d → N) (L : RunItems) (μ : Nat → N) (ar : AddrRule)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    {M : Module d} {f : Func d}
    (hfin : letI := DialectTrace.traceAt (d := d) lay ρ L
      OpsTraceFinite d (DialectTrace.Event d) (DialectTrace.Answer d) (TraceState N (unitsOf lay)))
    (hmono : letI := DialectTrace.traceAt (d := d) lay ρ L
      ∀ g ∈ M.funcs, g.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    (hf : letI := DialectTrace.traceAt (d := d) lay ρ L
      f.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)))
    {a a' : HVector toType (f.params.map (·.2))} (ha : a.Forall₂ TyRefinement.IsRefinedBy a') :
    traceObservable (f.traceRuns lay ρ L μ ar M a) ⊑ traceObservable (f.traceRuns lay ρ L μ ar M a') :=
  Func.traceRuns_isRefinedBy_of_args lay ρ L μ ar htrans hfin hmono hf ha

end FirTest.G0
