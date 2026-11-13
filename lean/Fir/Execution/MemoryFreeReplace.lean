import Fir.Execution.MemoryFreeRuns

/-!
# Congruence in a callee that touches no memory

Congruence in the callee with memory asks for one budget past which no run
of the new callee from any memories runs out of fuel unless it diverges (the
section on replacing a callee, with memory). For a callee whose effects
include no memory read, write or allocation, finitely many argument vectors
give that budget (the section on runs that touch no memory), as they do for
runs in the set monad. The human ruled on #373, on 2026-11-13, that the
core's congruence keeps this form for such a callee, and asks for the budget
only of a callee that touches memory, until
[#214](https://github.com/pmatos/funk/issues/214).

Wherever a run names the dialect's memories, when its ops ignore the
memories where they touch none:

* a function that reaches no memory returns from given memories
  what it returns with memory, with those memories, and hits UB or runs out
  of fuel from them exactly when it does with memory;
* so when an old and a new callee both reach no memory,
  refinement of their runs with memory is refinement of their runs from
  given memories, the memories they end with included: both end with the
  memories they start with.

For a dialect lawful in its monotonicity, in a valid module, congruence in
the callee then holds with no budget for a callee with finitely many
argument vectors whose new body, in the new module, reaches no memory: when the new callee refines the old from given memories,
or, when the old callee reaches no memory too, with memory. It
asks nothing of the new body but that.
-/

namespace Fir

open SetM Memory

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]

variable [DialectEffects d] [DialectMemDenote d] {N : Type} [DecidableEq N]
  (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N)

/-! # Runs from given memories are runs with memory -/

section

variable {M : Module d} {s : Name} {f : Func d}
  (hfree : letI := DialectMemDenote.denoteAt (d := d) lay ρ
    OpsIgnoreMemory d N (unitsOf lay))
  (hf : M.func? s = some f) (hs : M.table.ReachesNoMemory s)
  (a : HVector toType (f.params.map (·.2))) (S : Memories N (unitsOf lay)) (n : Nat)
include hfree hf hs

/-- A function that reaches no memory returns from given memories
what it returns with memory, with those memories. -/
theorem Func.memRunsFrom_ret_iff {vs : List (DVal d)} {S' : Memories N (unitsOf lay)} :
    letI := DialectMemDenote.denoteAt (d := d) lay ρ
    (f.memRunsFrom M (a, S) n).outcomes (.ret (vs, S')) ↔
      S' = S ∧ (f.memRuns lay ρ M a n).outcomes (.ret vs) := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Func.memRunsFrom_ignoresMemory hfree hf hs a S Memories.empty n
      (Ev.notStuck_ok _) h
    simp only [Ev.mapRet, atMem, Ev.ok.injEq, Except.ok.injEq, Result.ret.injEq, Prod.mk.injEq,
      true_and] at h1
    exact ⟨h1.symm, (Func.memRuns_ret_iff lay ρ).2 ⟨_, h2⟩⟩
  · rintro ⟨rfl, h⟩
    obtain ⟨T, hT⟩ := (Func.memRuns_ret_iff lay ρ).1 h
    exact (Func.memRunsFrom_ignoresMemory hfree hf hs a Memories.empty S' n (Ev.notStuck_ok _)
      hT).2

/-- A function that reaches no memory hits UB from given memories
exactly when it does with memory. -/
theorem Func.memRunsFrom_ub_iff {r : String} :
    letI := DialectMemDenote.denoteAt (d := d) lay ρ
    (f.memRunsFrom M (a, S) n).outcomes (.ub r) ↔ (f.memRuns lay ρ M a n).outcomes (.ub r) := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ
  exact ⟨fun h => (Func.memRuns_ub_iff lay ρ).2 (Func.memRunsFrom_ignoresMemory hfree hf hs a S
      Memories.empty n (Ev.notStuck_ub _) h).2,
    fun h => (Func.memRunsFrom_ignoresMemory hfree hf hs a Memories.empty S n (Ev.notStuck_ub _)
      ((Func.memRuns_ub_iff lay ρ).1 h)).2⟩

/-- A function that reaches no memory runs out of fuel from given
memories exactly when it does with memory. -/
theorem Func.memRunsFrom_exhausted_iff_memRuns :
    letI := DialectMemDenote.denoteAt (d := d) lay ρ
    (f.memRunsFrom M (a, S) n).outcomes .fuelExhausted ↔
      (f.memRuns lay ρ M a n).outcomes .fuelExhausted := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ
  exact (Func.memRunsFrom_exhausted_iff hfree hf hs a S Memories.empty n).trans
    (Func.memRuns_exhausted_iff lay ρ).symm

end

variable [TyRefinement d.Ty]

/-- When a function and the function with a new body both reach no
memory, the second refines the first from given memories, the
memories they end with included, when it refines it with memory. -/
theorem Func.memRunsFrom_isRefinedBy_of_memRuns
    (hfree : letI := DialectMemDenote.denoteAt (d := d) lay ρ
      OpsIgnoreMemory d N (unitsOf lay))
    {M M' : Module d} {s s' : Name} {f : Func d} {t : Name} {b : Region d}
    (hf : M.func? s = some f) (hs : M.table.ReachesNoMemory s)
    (hf' : M'.func? s' = some (f.replaceBody t b)) (hs' : M'.table.ReachesNoMemory s')
    (h : f.memRuns lay ρ M ⊑ (f.replaceBody t b).memRuns lay ρ M') :
    letI := DialectMemDenote.denoteAt (d := d) lay ρ
    f.memRunsFrom (Mem := N) (unit := unitsOf lay) M ⊑
      (f.replaceBody t b).memRunsFrom (Mem := N) (unit := unitsOf lay) M' := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ
  intro ⟨a, S⟩ o ho
  have ub_from : ∀ {r : String}, observable (f.memRuns lay ρ M a) (.ub r) →
      ∃ x, observable (f.memRunsFrom M (a, S)) x ∧ x ⊑ o :=
    fun ⟨k, hk⟩ => ⟨.ub _, ⟨k, (Func.memRunsFrom_ub_iff lay ρ hfree hf hs a S k).2 hk⟩, trivial⟩
  match o, ho with
  | .ret (vs', S''), ⟨n, hn⟩ =>
    obtain ⟨rfl, hn'⟩ := (Func.memRunsFrom_ret_iff lay ρ hfree hf' hs' a S n).1 hn
    obtain ⟨x, hx, hle⟩ := h a (.ret vs') ⟨n, hn'⟩
    match x, hx, hle with
    | .ub _, hx, _ => exact ub_from hx
    | .ret vs, ⟨k, hk⟩, hle =>
      exact ⟨.ret (vs, S''), ⟨k, (Func.memRunsFrom_ret_iff lay ρ hfree hf hs a S'' k).2 ⟨rfl, hk⟩⟩,
        hle, Memories.isRefinedBy_refl S''⟩
    | .fuelExhausted, _, hle => exact hle.elim
  | .ub r', ⟨n, hn⟩ =>
    obtain ⟨x, hx, hle⟩ :=
      h a (.ub r') ⟨n, (Func.memRunsFrom_ub_iff lay ρ hfree hf' hs' a S n).1 hn⟩
    match x, hx, hle with
    | .ub _, hx, _ => exact ub_from hx
    | .ret _, _, hle | .fuelExhausted, _, hle => exact hle.elim
  | .fuelExhausted, ho =>
    obtain ⟨x, hx, hle⟩ := h a .fuelExhausted fun n =>
      (Func.memRunsFrom_exhausted_iff_memRuns lay ρ hfree hf' hs' a S n).1 (ho n)
    match x, hx, hle with
    | .ub _, hx, _ => exact ub_from hx
    | .fuelExhausted, hx, _ =>
      exact ⟨.fuelExhausted, fun k =>
        (Func.memRunsFrom_exhausted_iff_memRuns lay ρ hfree hf hs a S k).2 (hx k), trivial⟩
    | .ret _, _, hle => exact hle.elim

/-! # Congruence in the callee, with no budget -/

variable [DialectValidation d] [LawfulDialectMonotone d] {M : Module d}

/-- Congruence in the callee, with memory, for a callee that touches no
memory, by the class alone: in a valid module, replacing the body of its
function `@g`, whose parameter types have finitely many argument vectors,
with one under which `@g`, run in the new module from given memories,
refines `@g` in the old, and under which it reaches no memory in the new
module, refines every function of the module, from given
memories and so with memory, wherever a run names the dialect's memories
and its ops ignore the memories where they touch none, calls and recursion
included. -/
theorem Func.memRuns_replaceBody_isRefinedBy_of_finite
    (hrefl : ∀ {t : d.Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    (hfree : letI := DialectMemDenote.denoteAt (d := d) lay ρ
      OpsIgnoreMemory d N (unitsOf lay))
    (hM : M.Valid) {g : Func d} (hg : g ∈ M.funcs) (b : Region d)
    (hfin : ∃ L : List (HVector toType (g.params.map (·.2))), ∀ a, a ∈ L)
    (hmem : (M.replaceBody g.name b).table.ReachesNoMemory g.name)
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ;
      g.memRunsFrom (Mem := N) (unit := unitsOf lay) M ⊑
        (g.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay) (M.replaceBody
            g.name b))
    {f : Func d} (hf : f ∈ M.funcs) :
    (letI := DialectMemDenote.denoteAt (d := d) lay ρ;
      f.memRunsFrom (Mem := N) (unit := unitsOf lay) M ⊑
        (f.replaceBody g.name b).memRunsFrom (Mem := N) (unit := unitsOf lay) (M.replaceBody
            g.name b)) ∧
      f.memRuns lay ρ M ⊑ (f.replaceBody g.name b).memRuns lay ρ (M.replaceBody g.name b) :=
  letI := DialectMemDenote.denoteAt (d := d) lay ρ
  Func.memRuns_replaceBody_isRefinedBy_of_bound lay ρ hrefl htrans hM hg b
    (Func.memRunsFrom_boundedBy_of_finite hfree
      (Module.func?_replaceBody_self hM.symbolsUnique hg b) hmem hfin) h hf

/-- Congruence in the callee, with memory, for a callee that touches no
memory before or after, by the class alone: as above, when `@g` reaches no
memory in the old module too, it is enough that `@g`, run
with memory in the new module, refine `@g` in the old. -/
theorem Func.memRuns_replaceBody_isRefinedBy_of_memRuns
    (hrefl : ∀ {t : d.Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    (hfree : letI := DialectMemDenote.denoteAt (d := d) lay ρ
      OpsIgnoreMemory d N (unitsOf lay))
    (hM : M.Valid) {g : Func d} (hg : g ∈ M.funcs) (b : Region d)
    (hfin : ∃ L : List (HVector toType (g.params.map (·.2))), ∀ a, a ∈ L)
    (hold : M.table.ReachesNoMemory g.name)
    (hmem : (M.replaceBody g.name b).table.ReachesNoMemory g.name)
    (h : g.memRuns lay ρ M ⊑ (g.replaceBody g.name b).memRuns lay ρ (M.replaceBody g.name b))
    {f : Func d} (hf : f ∈ M.funcs) :
    f.memRuns lay ρ M ⊑ (f.replaceBody g.name b).memRuns lay ρ (M.replaceBody g.name b) :=
  (Func.memRuns_replaceBody_isRefinedBy_of_finite lay ρ hrefl htrans hfree hM hg b hfin hmem
    (Func.memRunsFrom_isRefinedBy_of_memRuns lay ρ hfree
      (Module.func?_of_mem hM.symbolsUnique hg) hold
      (Module.func?_replaceBody_self hM.symbolsUnique hg b) hmem h) hf).2

end Fir
