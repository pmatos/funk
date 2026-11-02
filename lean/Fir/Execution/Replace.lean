import Fir.Execution.RefineRuns

/-!
# Congruence in the callee

The second of #20's function-level theorems: replacing a callee's body
refines every caller when the callee, run in the new module, refines the
old one, recursion included
(`Func.runs_replaceBody_isRefinedBy`; `Core.replaceBody_isRefinedBy` for
the core dialect).

_What replacing a callee means._ The module `M.replaceBody s b` is `M`
with the body `b` in place of the body of its function `@s`
(`Module.replaceBody`). Every function keeps its symbol, its parameters
and its result types, and every other function keeps its body. A caller
reaches a callee only by its symbol (ADR-2026-10-29-2012), so this
replaces the callee `@s` for every caller at once. The symbol table, and
so the context of validation, stays the same
(`Module.context_replaceBody`): the new module is valid when the old one
is and the new function is valid in that context
(`Module.valid_replaceBody`).

_The statement._ In a module `M` whose symbols are unique, as they are in
every valid module, let `@g` be a function of `M`, let `M'` be
`M.replaceBody g.name b`, and let `g'` be `@g` with the body `b`. If the
runs of `g'` in `M'` refine the runs of `g` in `M`, as
`FuncRuns.IsRefinedBy` asks of two functions, then each function `f` of
`M` is refined by its counterpart in `M'`: `f` itself, or `g'` when `f` is
`@g` (ADR-2026-11-02-1350).

The hypothesis compares `g'` in the new module with `g` in the old. A
callee that calls back, itself or its callers, calls the new body in
`M'`, so only its runs in `M'` say what a call of it does there. A weaker
hypothesis, that `g'` run in the old module refines `g`, would make the
theorem false. If `g` returns `0`, the body `call @g` refines it in `M`,
where it calls the old `@g`; in `M'` it calls itself, and never returns,
which does not refine a return. The hypothesis can be met when `@g`
calls back into the module, as the tests show, so recursion through the
replaced callee is included, and so are callers that call themselves.

The comparison is between real behaviours when `g'` is valid in the old
module's context. Then `M'` is valid when `M` is
(`Module.valid_replaceBody`), and for the core dialect no path of a run
in either module is stuck, and each run has an outcome at every budget
(`Core.neverStuck`, `Core.progress`). A body that gets stuck at once,
such as one whose entry block declares arguments, meets the hypothesis
with an empty behaviour, which refines every source (the section on
refinement), and every caller's paths through `@g` are then dropped.

_The proof._ Every call of the symbol `@g` is a black box, whose source is
`g` in `M` and whose target is `g'` in `M'`, and every other symbol names
the same function in both modules (`Module.func?_replaceBody`). The black
box refines: on arguments that refine others, `g` on them is refined by
`g` on the refined ones (the section on refined arguments), which is
refined by `g'` on those, by the hypothesis. So the previous section
gives the theorem for each `f` other than `@g`.

The black box needs its `bound`: on each argument vector, `g'` diverges,
or none of its runs with `bound` steps or more runs out of fuel. Each
argument vector has such a budget, since a run that runs out of fuel
with more steps runs out with fewer (`Func.runs_exhausted_down`). One
budget serves them all when `@g`'s parameter types have finitely many
argument vectors (`exists_common_bound`), as every core type has. The
proof needs this (ADR-2026-11-02-1426). Without it, one budget may not
bound them all: a caller whose arguments to `@g` grow without limit can
make `g'` run longer and longer before it returns. A dialect whose
choices each have finitely many options, as the section on observable
behaviour assumes, but which has a type of infinitely many values,
would need another argument, such as König's lemma over the tree of
choices.
-/

namespace Fir

open SetM

section

variable {d : Dialect}

/-- The function `f`, with the body `b` in place of its own when its symbol
is `s`. -/
abbrev Func.replaceBody (s : Name) (b : Region d) (f : Func d) : Func d :=
  { f with body := if f.name = s then b else f.body }

/-- The module `M`, with the body `b` in place of the body of its function
whose symbol is `s`: every other part of it is unchanged. -/
def Module.replaceBody (M : Module d) (s : Name) (b : Region d) : Module d :=
  ⟨M.items.map fun | .func f => .func (f.replaceBody s b), M.locs⟩

/-- The functions of `M` with a body replaced are those of `M`, each with
its body replaced when its symbol is `s`. -/
theorem Module.funcs_replaceBody (M : Module d) (s : Name) (b : Region d) :
    (M.replaceBody s b).funcs = M.funcs.map (Func.replaceBody s b) := by
  simp only [Module.replaceBody, Module.funcs, List.map_map]
  congr 1

/-- A function whose symbol is not `s` keeps its body. -/
theorem Func.replaceBody_of_ne {s : Name} {b : Region d} {f : Func d} (h : f.name ≠ s) :
    f.replaceBody s b = f := by
  simp [Func.replaceBody, h]

/-- The function `@s` gets the body `b`. -/
theorem Func.replaceBody_of_eq {s : Name} {b : Region d} {f : Func d} (h : f.name = s) :
    f.replaceBody s b = { f with body := b } := by
  simp [Func.replaceBody, h]

/-- The module with a body replaced finds the function it found, with its
body replaced when its symbol is `s`. -/
theorem Module.func?_replaceBody (M : Module d) (s : Name) (b : Region d) (x : Name) :
    (M.replaceBody s b).func? x = (M.func? x).map (Func.replaceBody s b) := by
  simp only [Module.func?, Module.funcs_replaceBody, List.find?_map]
  rfl

/-- In a module whose symbols are unique, a function of the module is the
one that its symbol finds. -/
theorem Module.func?_of_mem {M : Module d} (hnd : (M.funcs.map (·.name)).Nodup) {g : Func d}
    (hg : g ∈ M.funcs) : M.func? g.name = some g := by
  simp only [Module.func?]
  cases h : M.funcs.find? (·.name == g.name) with
  | none => exact absurd hg (by simpa using List.find?_eq_none.1 h g)
  | some k =>
    have hk := List.mem_of_find?_eq_some h
    have hn : k.name = g.name := by simpa using List.find?_some h
    rw [eq_of_nodup_map hnd hk hg hn]

/-- Replacing a body keeps the symbol table: every function keeps its
symbol and its type. -/
theorem Module.symbols_replaceBody (M : Module d) (s : Name) (b : Region d) :
    (M.replaceBody s b).symbols = M.symbols := by
  funext x
  simp only [Module.symbols, Module.funcs_replaceBody, List.find?_map, Option.map_map]
  rfl

/-- Replacing a body keeps the context in which the module's functions are
checked. -/
theorem Module.context_replaceBody (M : Module d) (s : Name) (b : Region d) :
    (M.replaceBody s b).context = M.context := by
  simp only [Module.context, Module.symbols_replaceBody]
  rfl

variable [DialectSignature d] [DialectValidation d]

/-- A valid module with a body replaced is valid when its function `@s`
with the new body is valid in the module's context, which the replacement
keeps. -/
theorem Module.valid_replaceBody {M : Module d} (hM : M.Valid) {s : Name} {b : Region d}
    (h : ∀ g ∈ M.funcs, g.name = s → ({ g with body := b } : Func d).Valid M.context) :
    (M.replaceBody s b).Valid where
  symbolsUnique := by
    rw [Module.funcs_replaceBody, List.map_map]
    exact hM.symbolsUnique
  locs := hM.locs
  funcs f hf := by
    rw [Module.context_replaceBody]
    rw [Module.funcs_replaceBody] at hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    by_cases hs : g.name = s
    · rw [Func.replaceBody_of_eq hs]
      exact h g hg hs
    · rw [Func.replaceBody_of_ne hs]
      exact hM.funcs g hg

end

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d SetM] [TyRefinement d.Ty]

omit [TyRefinement d.Ty] in
/-- A function's run that runs out of fuel runs out of fuel with fewer
steps. -/
theorem Func.runs_exhausted_down {M : Module d} {f : Func d}
    {a : HVector toType (f.params.map (·.2))} {n m : Nat} (h : n ≤ m)
    (hm : (f.runs M a m).outcomes .fuelExhausted) : (f.runs M a n).outcomes .fuelExhausted := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  obtain ⟨p, hp, hx⟩ := Func.runs_exh_inv hm
  exact Func.runs_of_runOps hp (Func.runOps_exhausted_down M n j f p.2 p.1 hx)

/-- On each of finitely many argument vectors, a run either runs out of fuel
at every budget, or from some budget on never does, when running out of
fuel at a budget implies it at every smaller one. Then one budget serves
them all. -/
theorem exists_common_bound {A : Type} {L : List A} (hL : ∀ a, a ∈ L) (Q : A → Nat → Prop)
    (hQ : ∀ a {m m' : Nat}, m ≤ m' → Q a m' → Q a m) :
    ∃ B, ∀ a, (∀ m, Q a m) ∨ ∀ m, B ≤ m → ¬ Q a m := by
  suffices h : ∀ L' : List A, ∃ B, ∀ a ∈ L', (∀ m, Q a m) ∨ ∀ m, B ≤ m → ¬ Q a m by
    obtain ⟨B, hB⟩ := h L
    exact ⟨B, fun a => hB a (hL a)⟩
  intro L'
  induction L' with
  | nil => exact ⟨0, fun _ h => nomatch h⟩
  | cons a L' ih =>
    obtain ⟨B, hB⟩ := ih
    by_cases hd : ∀ m, Q a m
    · exact ⟨B, fun c hc => (List.mem_cons.1 hc).elim (fun h => h ▸ .inl hd) (hB c)⟩
    · obtain ⟨m₀, hm₀⟩ := Classical.not_forall.1 hd
      refine ⟨max B m₀, fun c hc => (List.mem_cons.1 hc).elim (fun h => h ▸ .inr ?_) ?_⟩
      · exact fun m hm hq => hm₀ (hQ a (Nat.le_trans (Nat.le_max_right _ _) hm) hq)
      · intro hc
        rcases hB c hc with h | h
        · exact .inl h
        · exact .inr fun m hm => h m (Nat.le_trans (Nat.le_max_left _ _) hm)

/-- Congruence in the callee: in a module whose symbols are unique,
replacing the body of its function `@g` with one under which `@g`, run
in the new module, refines `@g` in the old, refines every function of the
module, calls and recursion included. It asks that every terminator and
every op with no callee be monotone, that the refinement of values be
reflexive and transitive, and that `@g` have finitely many argument
vectors. -/
theorem Func.runs_replaceBody_isRefinedBy
    (hmono : ∀ op : d.Op, isTerminator op = true ∨ callee? op = none → OpMonotone op)
    (hrefl : ∀ {t : d.Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    {M : Module d} (hnd : (M.funcs.map (·.name)).Nodup) {g : Func d} (hg : g ∈ M.funcs)
    (b : Region d) (hfin : ∃ L : List (HVector toType (g.params.map (·.2))), ∀ a, a ∈ L)
    (h : g.runs M ⊑ (g.replaceBody g.name b).runs (M.replaceBody g.name b))
    {f : Func d} (hf : f ∈ M.funcs) :
    f.runs M ⊑ (f.replaceBody g.name b).runs (M.replaceBody g.name b) := by
  by_cases hfg : f.name = g.name
  · rw [eq_of_nodup_map hnd hf hg hfg]
    exact h
  show f.runs M ⊑ Func.runs _ { f with body := if f.name = g.name then b else f.body }
  rw [ite_eq_right hfg]
  obtain ⟨L, hL⟩ := hfin
  obtain ⟨bound, hbound⟩ := exists_common_bound hL
    (fun a m =>
      ((g.replaceBody g.name b).runs (M.replaceBody g.name b) a m).outcomes .fuelExhausted)
    (fun _ _ _ hle hq => Func.runs_exhausted_down hle hq)
  have hobs : ∀ {x y z : List (DVal d)}, x ⊑ y → y ⊑ z → x ⊑ z :=
    List.isRefinedBy_trans (DVal.isRefinedBy_trans htrans)
  have bb : BlackBox M (M.replaceBody g.name b) bound g (g.replaceBody g.name b) :=
    { params := rfl
      refines := fun a a' ha => Behaviour.isRefinedBy_trans hobs
        (Func.runs_args_isRefinedBy hmono M g ha) (h a')
      bounded := hbound }
  have hcalls : CallsRefined M (M.replaceBody g.name b) bound := by
    intro x
    by_cases hx : x = g.name
    · subst hx
      refine .inr ⟨g, _, Module.func?_of_mem hnd hg, ?_, bb⟩
      rw [Module.func?_replaceBody, Module.func?_of_mem hnd hg]
      rfl
    · refine .inl ?_
      rw [Module.func?_replaceBody]
      cases hk : M.func? x with
      | none => rfl
      | some k =>
        have hn : k.name = x := by simpa using List.find?_some hk
        simp only [Option.map_some, Func.replaceBody_of_ne (hn ▸ hx : k.name ≠ g.name)]
  exact fun a => Func.runs_isRefinedBy_of_calls hmono hcalls f
    (HVector.forall₂_refl (fun v => hrefl v) a)

end Fir
