import Fir.Execution.MemoryFiniteDown
import Fir.Execution.MemoryReplace

/-!
# Congruence in the callee with ops of finitely many outcomes

The refinement theorem for runs from given memories, with black boxes, holds
with no budget when every op that runs by its own rule has finitely many
outcomes. Each return and each UB of the target is allowed by the source,
as in the section on refined arguments and memories. A target that
diverges runs out of fuel at every budget. If the source hits UB at some
budget, that allows it. If not, the source runs out of fuel at every budget:
at a budget where it did not, some budget of the target would not either, by
the section on divergence with ops of finitely many outcomes.

So congruence in the callee with memory asks for no budget for the new
callee, whatever its parameter types and whatever it does to the memories:
the new `@g`, run in the new module from given memories, refines `@g` in the
old, and the ops of the dialect have finitely many outcomes. This is the
form that the decisions record names
(`docs/decisions/semantics-refinement.md#congruence-in-the-callee`).
-/

namespace Fir

open SetM Memory

section

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (StateT (Memories Mem unit) SetM)] [TyRefinement d.Ty]

/-- A function's behaviour from given memories in the target module, on
arguments that refine others and from memories that refine others, refines
its behaviour from those others in the source module, the memories they end
with included, when every call names the same function in both modules or a
black box with memory, every op that runs by its own rule has finitely many
outcomes, and every terminator and every op with no callee of the function
and of the source module's functions is monotone with memory. No black box
needs a budget. -/
theorem Func.memRunsFrom_isRefinedBy_of_opsFinite {M M' : Module d}
    (hmono : ∀ g ∈ M.funcs, g.MemOpsMonotone Mem unit) (hfin : OpsFinite d Mem unit)
    (hcalls : MemCallsRefined Mem unit M M') (f : Func d) (hf : f.MemOpsMonotone Mem unit)
    {a a' : HVector toType (f.params.map (·.2))} (ha : a.Forall₂ TyRefinement.IsRefinedBy a')
    {S S' : Memories Mem unit} (hS : S ⊑ S') :
    observable (f.memRunsFrom M (a, S)) ⊑ observable (f.memRunsFrom M' (a', S')) := by
  have start : ∀ {p' : List (Operation d) × Env d}, f.enter a'.toDVals = .ok p' →
      ∃ genv, f.enter a.toDVals = .ok (p'.1, genv) ∧ genv.IsRefinedBy p'.2 :=
    fun hen' => Func.enter_isRefinedBy (HVector.toDVals_isRefinedBy ha) hen'
  have back : ∀ {p : List (Operation d) × Env d} {N : Nat}
      {e : Ev (Except Stuck (Result ((List (DVal d) × Memories Mem unit) × Nat)))},
      Ev.NotStuck e.dropLeft → f.enter a.toDVals = .ok p →
      (Func.memCall M N f p.2 p.1 S).run e → (f.memRunsFrom M (a, S) N) e.dropLeft :=
    fun hne hen h => (Func.memRunsFrom_run hne).2 ⟨_, hen, _, h, rfl⟩
  intro t ht
  match t, ht with
  | .ret o, ht =>
    exact Func.memRunsFrom_retUB_allowed hmono hcalls f hf ha hS _ (fun h => nomatch h) ht
  | .ub r, ht =>
    exact Func.memRunsFrom_retUB_allowed hmono hcalls f hf ha hS _ (fun h => nomatch h) ht
  | .fuelExhausted, ht =>
    classical
    by_cases hU : ∃ N r, (f.memRunsFrom M (a, S) N).outcomes (.ub r)
    · obtain ⟨N, r, h⟩ := hU
      exact ⟨.ub r, ⟨N, h⟩, trivial⟩
    refine ⟨.fuelExhausted, fun N => Classical.byContradiction fun hN => ?_, trivial⟩
    have hexh : ∀ n, ∃ p', f.enter a'.toDVals = .ok p' ∧
        (Func.memCall M' n f p'.2 p'.1 S').run (.ok (.ok .fuelExhausted)) := fun n => by
      obtain ⟨p', hen', e', he', hx⟩ := (Func.memRunsFrom_run (x := .ok (.ok .fuelExhausted))
        (fun _ h => nomatch h)).1 (ht n)
      match e', he', hx with
      | .ok (.ok .fuelExhausted), he', _ => exact ⟨p', hen', he'⟩
    obtain ⟨p', hen', -⟩ := hexh 0
    obtain ⟨genv, hen, henv⟩ := start hen'
    obtain ⟨n, hn⟩ := Func.memOps_notExhausted_of_finite hmono hfin hcalls N f genv p'.2 p'.1
      S.enter S'.enter hf (hf.enter hen') henv hS.enter
      (fun ⟨N, r, h⟩ => hU ⟨N, r, back (e := .ub r) (fun _ h => nomatch h) hen
        (Func.memCall_ub_of_memOps h)⟩)
      (fun h => hN (back (e := .ok (.ok .fuelExhausted)) (fun _ h => nomatch h) hen
        (Func.memCall_exhausted_iff.2 h)))
    obtain ⟨p'', hen'', h⟩ := hexh n
    rw [hen'] at hen''
    cases hen''
    exact hn (Func.memCall_exhausted_iff.1 h)

/-- Congruence in the callee, with memory, with ops of finitely many
outcomes: in a module whose symbols are unique, replacing the body of its
function `@g` with one under which `@g`, run in the new module from given
memories, refines `@g` in the old, refines every function of the module
from given memories, calls and recursion included. It asks that every op
that runs by its own rule have finitely many outcomes, that every terminator
and every op with no callee of the old module's functions be monotone with
memory, and that the refinement of values be reflexive and transitive. It
asks for no budget, whatever the parameter types of `@g` and whatever its
new body does to the memories. -/
theorem Func.memRunsFrom_replaceBody_isRefinedBy_of_opsFinite {M : Module d}
    (hmono : ∀ g ∈ M.funcs, g.MemOpsMonotone Mem unit) (hfin : OpsFinite d Mem unit)
    (hrefl : ∀ {t : d.Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    (hnd : (M.funcs.map (·.name)).Nodup) {g : Func d} (hg : g ∈ M.funcs) (b : Region d)
    (h : g.memRunsFrom (Mem := Mem) (unit := unit) M ⊑
      (g.replaceBody g.name b).memRunsFrom (Mem := Mem) (unit := unit) (M.replaceBody g.name b))
    {f : Func d} (hf : f ∈ M.funcs) :
    f.memRunsFrom (Mem := Mem) (unit := unit) M ⊑
      (f.replaceBody g.name b).memRunsFrom (Mem := Mem) (unit := unit) (M.replaceBody g.name b) := by
  by_cases hfg : f.name = g.name
  · rw [eq_of_nodup_map hnd hf hg hfg]
    exact h
  show f.memRunsFrom M ⊑ Func.memRunsFrom _ { f with body := if f.name = g.name then b else f.body }
  rw [ite_eq_right hfg]
  exact fun p => Func.memRunsFrom_isRefinedBy_of_opsFinite hmono hfin
    (Module.replaceBody_memCallsRefined hmono htrans hnd hg b h) f (hmono f hf)
    (HVector.forall₂_refl (fun v => hrefl v) p.1) (Memories.isRefinedBy_refl p.2)

end

/-! # What the class gives -/

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectEffects d] [DialectMemDenote d] [DialectValidation d] [TyRefinement d.Ty]
  [LawfulDialectMonotone d] {N : Type} [DecidableEq N] (lay : N → MemLayout)
  (ρ : DialectEffects.Mem d → N) {M : Module d}

/-- Congruence in the callee, with memory, by the class alone, with ops of
finitely many outcomes: in a valid module, replacing the body of its
function `@g` with one under which `@g`, run in the new module from given
memories, refines `@g` in the old, refines every function of the module,
from given memories and so with memory, wherever a run names the dialect's
memories, calls and recursion included, whatever the new body. It asks that
the refinement of values be reflexive and transitive, and that every op that
runs by its own rule have finitely many outcomes at that naming; it asks for
no budget. -/
theorem Func.memRuns_replaceBody_isRefinedBy_of_opsFinite
    (hrefl : ∀ {t : d.Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    (hfin : letI := DialectMemDenote.denoteAt (d := d) lay ρ; OpsFinite d N (unitsOf lay))
    (hM : M.Valid) {g : Func d} (hg : g ∈ M.funcs) (b : Region d)
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ;
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) M ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay) (M.replaceBody
            g.name b))
    {f : Func d} (hf : f ∈ M.funcs) :
    (letI := DialectMemDenote.denoteAt (d := d) lay ρ;
      f.memRunsFrom (Mem := N) (unit := unitsOf lay) M ⊑
        (f.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay) (M.replaceBody
            g.name b)) ∧
      f.memRuns lay ρ M ⊑ (f.replaceBody g.name b).memRuns lay ρ (M.replaceBody g.name b) := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ
  have hmono := fun g (hg : g ∈ M.funcs) => (hM.funcs g hg).memOpsMonotone
    (fun op hvo hc => LawfulDialectMonotone.monotone op hvo hc lay ρ)
  have hr := Func.memRunsFrom_replaceBody_isRefinedBy_of_opsFinite hmono hfin hrefl htrans
    hM.symbolsUnique hg b h hf
  exact ⟨hr, fun a => Func.memRuns_isRefinedBy_of_from lay ρ (hr (a, Memories.empty))⟩

end Fir
