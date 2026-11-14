import Fir.Execution.RefineRuns

/-!
# Congruence in the callee

The second of the two refinement theorems for whole functions: replacing
a callee's body refines every caller when the callee, run in the new
module, refines the old one, recursion included. The section on
refinement through core calls states it for the core dialect.

_What replacing a callee means._ Replacing the body of the function `@g`
of a module gives the same module with a new body in place of the body of
`@g`. Every function keeps its symbol, its parameters and its result
types, and every other function keeps its body. A caller reaches a callee
only by its symbol (ADR-2026-10-29-2012), so this replaces the callee
`@g` for every caller at once. The symbol table, and so the context of
validation, stays the same, and so do the dialect set and the data layout:
the new module is valid when the old one is and the new function is valid
in that context, with its types naming memories that the layout declares.

_The statement._ In a module whose symbols are unique, as they are in
every valid module, let `@g` be a function of the module, and replace its
body: the new function is `@g` with the new body. If the runs of the new
function in the new module refine the runs of `@g` in the old, as
refinement of functions asks, then each function of the old module is
refined by its counterpart in the new one: itself, or the new function
when it is `@g` (`docs/decisions/semantics-refinement.md#congruence-in-the-callee`).

The hypothesis compares the new function in the new module with `@g` in
the old. A callee that calls back, itself or its callers, calls the new
body in the new module, so only its runs there say what a call of it does
there. A weaker hypothesis, that the new function run in the old module
refines `@g`, would make the theorem false. If `@g` returns `0`, the body
`call @g` refines it in the old module, where it calls the old `@g`; in
the new module it calls itself, and never returns, which does not refine
a return. The hypothesis can be met when `@g` calls back into the module,
as the tests show, so recursion through the replaced callee is included,
and so are callers that call themselves.

The comparison is between real behaviours when the new function is valid
in the old module's context. Then the new module is valid when the old
one is, and for the core dialect no path of a run in either module is
stuck, and each run has an outcome at every budget (the section on core
functions with calls). A body that gets stuck at once, such as one whose
entry block declares arguments, meets the hypothesis with an empty
behaviour, which refines every source (the section on refinement), and
every caller's paths through `@g` are then dropped.

_The proof._ Every call of the symbol `@g` is a black box, whose source
is `@g` in the old module and whose target is the new function in the new
module, and every other symbol names the same function in both modules.
The black box refines: on arguments that refine others, `@g` on them is
refined by `@g` on the refined ones (the section on refined arguments),
which is refined by the new function on those, by the hypothesis. So the
previous section gives the theorem for each function other than `@g`.

Monotonicity is asked only of the old module's functions: the engine runs
ops of the target that it also finds in the source, and a call of `@g` is
a black box, whose new body it does not run. So a dialect whose ops are
monotone only at valid op instances meets it for every valid module,
whatever the new body (the section on what the lawful class gives).

The black box needs its bound: on each argument vector, the new function
diverges, or from some budget on never runs out of fuel. Each argument
vector has such a budget, since a run that runs out of fuel with more
steps runs out with fewer. One budget serves them all when the parameter
types of `@g` have finitely many argument vectors, as every core type
has. The proof needs this
(`docs/decisions/semantics-refinement.md#congruence-in-the-callee`). Without it, one budget
may not bound them all: a caller whose arguments to `@g` grow without
limit can make the new function run longer and longer before it returns.
A dialect whose choices each have finitely many options, as the section
on outcomes and behaviours assumes, but which has a type of infinitely
many values, would need another argument, such as König's lemma over the
tree of choices.
-/

namespace Fir

open SetM

section

variable {d : Dialect}

/-- The function `f`, with the body `b` in place of its own when its symbol
is `s`. -/
abbrev Func.replaceBody (s : Name) (b : Region d) (f : Func d) : Func d :=
  { f with body := if f.name = s then b else f.body }

/-- An item, with the body `b` in place of its body when it is a function
whose symbol is `s`. A nested module is unchanged: its functions are in its
own symbol table. An item of a dialect's kind is unchanged too. -/
def Item.replaceBody (s : Name) (b : Region d) : Item d → Item d
  | .func f => .func (f.replaceBody s b)
  | i => i

/-- The module `M`, with the body `b` in place of the body of its function
whose symbol is `s`: every other part of it is unchanged. -/
def Module.replaceBody (M : Module d) (s : Name) (b : Region d) : Module d :=
  ⟨M.dialects, M.layout, M.items.map (Item.replaceBody s b), M.locs⟩

/-- The functions of `M` with a body replaced are those of `M`, each with
its body replaced when its symbol is `s`. -/
theorem Module.funcs_replaceBody (M : Module d) (s : Name) (b : Region d) :
    (M.replaceBody s b).funcs = M.funcs.map (Func.replaceBody s b) := by
  simp only [Module.replaceBody, Module.funcs, List.filterMap_map, List.map_filterMap]
  congr 1
  funext i
  cases i <;> rfl

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

/-- The function `@g` of a module whose symbols are unique is, with its new
body, the function of the module with that body that `@g`'s symbol names. -/
theorem Module.func?_replaceBody_self {M : Module d} (hnd : (M.funcs.map (·.name)).Nodup)
    {g : Func d} (hg : g ∈ M.funcs) (b : Region d) :
    (M.replaceBody g.name b).func? g.name = some (g.replaceBody g.name b) := by
  rw [Module.func?_replaceBody, Module.func?_of_mem hnd hg]
  rfl

/-- A symbol other than `s` names the same function in the module with a
body replaced as in the module. -/
theorem Module.func?_replaceBody_of_ne {M : Module d} {s x : Name} {b : Region d} (hx : x ≠ s) :
    (M.replaceBody s b).func? x = M.func? x := by
  rw [Module.func?_replaceBody]
  cases hk : M.func? x with
  | none => rfl
  | some k =>
    have hn : k.name = x := by simpa using List.find?_some hk
    simp only [Option.map_some, Func.replaceBody_of_ne (hn ▸ hx : k.name ≠ s)]

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

/-- Replacing a body keeps every symbol of the module's own table. -/
theorem Item.name_replaceBody (s : Name) (b : Region d) (i : Item d) :
    (i.replaceBody s b).name = i.name := by
  cases i <;> rfl

/-- Replacing a body keeps the items of a dialect's kind of the module's own
table. -/
theorem Module.dialectItems_replaceBody (M : Module d) (s : Name) (b : Region d) :
    (M.replaceBody s b).table.dialectItems = M.table.dialectItems := by
  simp only [SymbolTable.dialectItems, Module.table, Module.replaceBody, List.filterMap_map]
  congr 1
  funext i
  cases i <;> rfl

/-- Replacing a body keeps the tables nested in the module's items: no
function holds one, and a nested module is unchanged. -/
theorem Item.tablesIn_replaceBody (s : Name) (b : Region d) :
    ∀ is : List (Item d), Item.tablesIn (is.map (Item.replaceBody s b)) = Item.tablesIn is
  | [] => rfl
  | i :: is => by
    rw [List.map_cons, Item.tablesIn, Item.tablesIn, Item.tablesIn_replaceBody s b is]
    cases i <;> rfl

variable [DialectSignature d] [DialectValidation d]

/-- A valid module with a body replaced is valid when its function `@s`
with the new body is valid in the module's context, which the replacement
keeps, and the module's layout declares the memories of its types. -/
theorem Module.valid_replaceBody {M : Module d} (hM : M.Valid) {s : Name} {b : Region d}
    (h : ∀ g ∈ M.funcs, g.name = s → ({ g with body := b } : Func d).Valid M.context)
    (hm : ∀ g ∈ M.funcs, g.name = s →
      ∀ ty ∈ ({ g with body := b } : Func d).types, M.layout.HasMemoryOf ty) :
    (M.replaceBody s b).Valid := by
  refine ⟨hM.locs, fun t ht => ?_, hM.layout, fun t ht => ?_⟩
  rotate_left
  · simp only [Module.tables, Module.replaceBody, Item.tablesIn_replaceBody, List.mem_cons] at ht
    rcases ht with rfl | ht
    · refine ⟨fun f hf => ?_, fun i hi => ?_⟩
      · have hf' : f ∈ (M.replaceBody s b).funcs := hf
        rw [Module.funcs_replaceBody] at hf'
        obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf'
        by_cases hs : g.name = s
        · rw [Func.replaceBody_of_eq hs]
          exact hm g hg hs
        · rw [Func.replaceBody_of_ne hs]
          exact (hM.memories _ (List.mem_cons_self ..)).funcs g hg
      · have hi' : i ∈ (M.replaceBody s b).table.dialectItems := hi
        rw [Module.dialectItems_replaceBody] at hi'
        exact (hM.memories _ (List.mem_cons_self ..)).dialectItems i hi'
    · exact hM.memories t (List.mem_cons_of_mem _ ht)
  simp only [Module.tables, Module.replaceBody, Item.tablesIn_replaceBody, List.mem_cons] at ht
  rcases ht with rfl | ht
  · refine ⟨?_, fun f hf => ?_, fun i hi => ?_, hM.dialectNames, hM.dialectsUnique⟩
    · change ((M.items.map (Item.replaceBody s b)).map Item.name).Nodup
      rw [List.map_map]
      have : Item.name ∘ Item.replaceBody s b = (Item.name : Item d → Name) :=
        funext (Item.name_replaceBody s b)
      rw [this]
      exact hM.table.symbolsUnique
    · have hc := Module.context_replaceBody M s b
      have hf' : f ∈ (M.replaceBody s b).funcs := hf
      change f.Valid (M.replaceBody s b).context
      rw [hc]
      rw [Module.funcs_replaceBody] at hf'
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf'
      by_cases hs : g.name = s
      · rw [Func.replaceBody_of_eq hs]
        exact h g hg hs
      · rw [Func.replaceBody_of_ne hs]
        exact hM.funcs g hg
    · have hi' : i ∈ (M.replaceBody s b).table.dialectItems := hi
      rw [Module.dialectItems_replaceBody] at hi'
      change i.Valid ⟨(M.replaceBody s b).symbols⟩
      rw [Module.symbols_replaceBody]
      exact hM.table.dialectItems i hi'
  · exact hM.tables t (List.mem_cons_of_mem _ ht)

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
    classical
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
every op with no callee of the old module's functions be monotone, that
the refinement of values be reflexive and transitive, and that `@g` have
finitely many argument vectors. -/
theorem Func.runs_replaceBody_isRefinedBy {M : Module d}
    (hmono : ∀ g ∈ M.funcs, g.OpsMonotone)
    (hrefl : ∀ {t : d.Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    (hnd : (M.funcs.map (·.name)).Nodup) {g : Func d} (hg : g ∈ M.funcs)
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
        (Func.runs_args_isRefinedBy M hmono g (hmono g hg) ha) (h a')
      bounded := hbound }
  have hcalls : CallsRefined M (M.replaceBody g.name b) bound := by
    intro x
    by_cases hx : x = g.name
    · subst hx
      exact .inr ⟨g, _, Module.func?_of_mem hnd hg, Module.func?_replaceBody_self hnd hg b, bb⟩
    · exact .inl (Module.func?_replaceBody_of_ne hx)
  exact fun a => Func.runs_isRefinedBy_of_calls hmono hcalls f (hmono f hf)
    (HVector.forall₂_refl (fun v => hrefl v) a)

end Fir
