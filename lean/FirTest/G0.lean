import Fir
import FirRef

/-!
G0's check on the Lean side (ADR-2026-11-03-0600). fir's spec is written
once for every dialect: its parser and printer, its validation and its
interpreter take the dialect as a parameter, and see a dialect's ops only
through the dialect's classes, so the dialect's `decodeOp` and `opAttrs`
hold its text. Each statement below is made of an arbitrary dialect `d`,
with the spec's own proof or definition. It builds only while those stay
parameterized over the dialect: narrowing one of them to the core dialect
breaks this file. `scripts/check_g0.py` checks the other half, that the
code of the spec's chapters for every dialect names nothing of the core
dialect and writes none of its words. It checks this file too, outside its
`#guard` commands, so a statement below cannot be narrowed to the core
dialect.

The section on behaviour models shows the seam where a dialect that needs
probabilities plugs in. `lean/FirTest/G0Effects.lean` restates the classes
of poison and effects, and the summaries of functions, in the same way.
-/

namespace FirTest.G0

open Fir

/-! # The text format -/

/-- The parser reads a module of any dialect. -/
example (d : Dialect) [DialectText d] : Parser d := Fir.parse

/-- The printer writes a module of any dialect. -/
example (d : Dialect) [DialectText d] : Module d → String := Module.print

/-- `fir-ref` reads the bytes of a file as a module of any dialect. -/
example (d : Dialect) [DialectText d] : ByteArray → Except ParseError (Module d) :=
  FirRef.parseBytes

/-- `fir-ref`'s parser is the spec's, for every dialect. -/
theorem firRef_parse (d : Dialect) [DialectText d] (t : String) :
    FirRef.parse (d := d) t = Fir.parse t := by
  rw [FirRef.parse_eq_parse]

/-- `fir-ref`'s printer is the spec's, for every dialect. -/
theorem firRef_print (d : Dialect) [DialectText d] (m : Module d) :
    FirRef.printModule m = m.print := by
  rw [FirRef.print_eq_printModule]

/-- `parse(print(m)) == m` for every well-formed module of every dialect
whose text is lawful. -/
theorem printThenParse (d : Dialect) [DialectSignature d] [DialectValidation d] [DialectText d]
    [LawfulDialectText d] : PrintThenParse (d := d) Fir.parse :=
  Fir.printThenParse

/-- `print(parse(t)) == t` for every text printed from a well-formed module
of every dialect whose text is lawful. -/
theorem parseThenPrint (d : Dialect) [DialectSignature d] [DialectValidation d] [DialectText d]
    [LawfulDialectText d] : ParseThenPrint (d := d) Fir.parse :=
  Fir.parseThenPrint

/-- What the parser reads is well formed, for every dialect whose text is
lawful. -/
theorem parse_wellFormed (d : Dialect) [DialectSignature d] [DialectValidation d] [DialectText d]
    [LawfulDialectText d] {t : String} {m : Module d} (h : Fir.parse t = .ok m) : m.WellFormed :=
  Fir.parse_wellFormed h

/-- Every valid module of every dialect whose text is lawful is well
formed. -/
theorem validIsWellFormed (d : Dialect) [DialectSignature d] [DialectValidation d] [DialectText d]
    [LawfulDialectText d] : ValidIsWellFormed (d := d) :=
  Fir.validIsWellFormed

/-! # Validation -/

/-- The validation check decides validity for every dialect whose rules
are decidable. -/
theorem problems_eq_nil_iff (d : Dialect) [DialectSignature d] [DialectValidation d]
    [DecidableEq d.Ty] [DecidableDialectValidation d] (m : Module d) :
    m.problems = [] ↔ m.Valid :=
  m.problems_eq_nil_iff

/-- The check of a module's dialect set decides its rule, for every dialect
with a text and a dialect set: the set names dialects of the dialect's own
set, and every word of the module names the core or a dialect of its set. -/
theorem setProblems_eq_nil_iff (d : Dialect) [DialectText d] [DialectSet d] (m : Module d) :
    m.setProblems = [] ↔ m.InDialectSet :=
  m.setProblems_eq_nil_iff

/-- `fir-ref`'s check of a module's dialect set is the spec's, for every
dialect. -/
theorem firRef_setProblems (d : Dialect) [DialectText d] [DialectSet d] (m : Module d) :
    FirRef.moduleSetProblems m = m.setProblems := by
  rw [FirRef.setProblems_eq_moduleSetProblems]

/-- A valid function obeys its dialect's own rule over a whole function, for
every dialect. -/
theorem validFunc_of_valid (d : Dialect) [DialectSignature d] [DialectValidation d]
    {ctx : ModuleContext d} {f : Func d} (h : f.Valid ctx) :
    validFunc (DialectView.id d) ⟨ctx.symbols⟩ f :=
  h.dialect

/-! # Execution -/

/-- The interpreter runs a function of any dialect, in any monad that has
the dialect's semantics and runs a call in a frame. -/
example (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
    (m : Type → Type) [Monad m] [MonadFrame m] [DialectDenote d m] (M : Module d) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) :
    ExceptT Stuck m (Result (List (DVal d))) :=
  f.run M args fuel

/-- More fuel never changes how a run ends, for every function of every
dialect. -/
theorem fuelMonotone (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
    [DialectCall d] [DialectDenote d SetM] (M : Module d) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) : FuelMonotone (f.runs M args) :=
  Func.fuelMonotone M f args

/-- No path of a run is stuck, for every function of every dialect whose
module's functions are valid and run within the module. -/
theorem neverStuck (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
    [DialectCall d] [DialectDenote d SetM] [DialectValidation d] {ctx : ModuleContext d}
    {M : Module d} (hv : ∀ g ∈ M.funcs, g.Valid ctx) (hm : ∀ g ∈ M.funcs, g.InModule M)
    {f : Func d} (hf : f ∈ M.funcs) (args : HVector toType (f.params.map (·.2))) :
    NeverStuck (f.runs M args) :=
  Func.neverStuck_of_inModule hv hm hf args

/-- A run has an outcome at every budget, for every function of every
dialect whose ops meet the poison obligations, when its module's functions
are valid and run within the module. -/
theorem progress (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty] [TyPoison d.Ty]
    [TyRefinement d.Ty] [DialectSignature d] [DialectValidation d] [DialectEffects d]
    [DialectCall d] [DialectDenote d SetM] [LawfulDialectPoison d] {ctx : ModuleContext d}
    {M : Module d} (hv : ∀ g ∈ M.funcs, g.Valid ctx) (hm : ∀ g ∈ M.funcs, g.InModule M)
    {f : Func d} (hf : f ∈ M.funcs) (args : HVector toType (f.params.map (·.2))) :
    Progress (f.runs M args) :=
  Func.progress_of_lawful hv hm hf args

/-! # Behaviour models

The core dialect's behaviour is a set of outcomes, and a dialect that needs
probabilities supplies its own behaviour model (ADR-2026-11-09-1322). The
seam is the interpreter's genericity over its monad and a monad morphism
out of a tree of choices. The toy below goes through that seam: a tree of
weighted choices, a finite distribution, and a morphism between them.
-/

/-- A toy tree of weighted choices. `flip p h t` goes on with `h` with
weight `p`, and with `t` with weight `1 - p`. -/
inductive WeightedTree (α : Type) where
  | pure (a : α)
  | flip (p : Rat) (heads tails : WeightedTree α)

/-- Runs `f` on the result of each path of a tree. -/
def WeightedTree.bind : WeightedTree α → (α → WeightedTree β) → WeightedTree β
  | .pure a, f => f a
  | .flip p h t, f => .flip p (h.bind f) (t.bind f)

instance : Monad WeightedTree where
  pure := .pure
  bind := WeightedTree.bind

/-- A finite distribution: the results it may give, each with its weight. -/
def Dist (α : Type) : Type := List (α × Rat)

/-- The results of a distribution, with their weights. -/
def Dist.entries (d : Dist α) : List (α × Rat) := d

/-- Multiplies every weight by `w`. -/
def Dist.scale (w : Rat) (d : Dist α) : Dist α :=
  d.entries.map fun y => (y.1, w * y.2)

/-- The results of `a` and then those of `b`. -/
def Dist.append (a b : Dist α) : Dist α := a.entries ++ b.entries

instance : Monad Dist where
  pure a := [(a, 1)]
  bind d f := d.entries.flatMap fun x => (Dist.scale x.2 (f x.1)).entries

/-- The distribution of a tree's paths: each result, weighted by the product
of the weights along its path. -/
def WeightedTree.toDist : WeightedTree α → Dist α
  | .pure a => [(a, 1)]
  | .flip p h t => (Dist.scale p h.toDist).append (Dist.scale (1 - p) t.toDist)

theorem Dist.scale_bind (w : Rat) (d : Dist α) (f : α → Dist β) :
    Dist.scale w d >>= f = Dist.scale w (d >>= f) := by
  show List.flatMap _ (List.map _ d.entries) = List.map _ (List.flatMap _ d.entries)
  simp only [List.flatMap_map, List.map_flatMap]
  congr 1
  funext x
  show List.map _ (f x.1).entries = List.map _ (List.map _ (f x.1).entries)
  rw [List.map_map]
  simp [Function.comp_def, Rat.mul_assoc]

theorem Dist.append_bind (a b : Dist α) (f : α → Dist β) :
    a.append b >>= f = (a >>= f).append (b >>= f) :=
  List.flatMap_append ..

theorem WeightedTree.toDist_bind (t : WeightedTree α) (f : α → WeightedTree β) :
    (t.bind f).toDist = t.toDist >>= fun a => (f a).toDist := by
  induction t with
  | pure a =>
    show (f a).toDist = List.flatMap _ [(a, (1 : Rat))]
    simp [Dist.scale, Dist.entries]
    rfl
  | flip p h t ihh iht =>
    simp only [WeightedTree.bind, WeightedTree.toDist, Dist.append_bind, Dist.scale_bind, ihh, iht]

/-- Neither the weighted tree nor the distribution monad has memory, so a
frame is the computation itself. -/
instance : MonadFrame WeightedTree := ⟨fun t => t⟩

instance : MonadFrame Dist := ⟨fun t => t⟩

/-- `toDist` is a monad morphism from the weighted tree to the distribution
monad: the same shape as `ChoiceTree.toSetMorphism`, with a distribution in
the place of a set. -/
def WeightedTree.toDistMorphism : MonadMorphism WeightedTree Dist where
  map := WeightedTree.toDist
  map_pure _ := rfl
  map_bind := WeightedTree.toDist_bind
  map_map g t := WeightedTree.toDist_bind t (fun a => .pure (g a))

/-- The interpreter runs a function of any dialect in the weighted tree, and
the morphism carries that run to its run in the distribution monad, as it
does for the set monad. -/
theorem weightedRun (d : Dialect) [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
    [DialectCall d] [DialectDenote d WeightedTree] [DialectDenote d Dist]
    (h : WeightedTree.toDistMorphism.MapsDenote (d := d)) (M : Module d) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) :
    (WeightedTree.toDistMorphism.except Stuck).map (f.run M (m := WeightedTree) args fuel) =
      f.run M (m := Dist) args fuel :=
  Func.run_map h (fun _ => rfl) M f args fuel

/-- The total weight of a distribution. -/
def Dist.mass (d : Dist α) : Rat :=
  d.entries.foldr (fun x s => x.2 + s) 0

theorem Dist.mass_scale (w : Rat) (d : Dist α) : (Dist.scale w d).mass = w * d.mass := by
  show List.foldr _ _ (List.map _ d.entries) = w * List.foldr _ _ d.entries
  induction d.entries with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.foldr_cons, ih, Rat.mul_add]

theorem Dist.mass_append (a b : Dist α) : (a.append b).mass = a.mass + b.mass := by
  show List.foldr _ _ (a.entries ++ b.entries) =
    List.foldr _ _ a.entries + List.foldr _ _ b.entries
  induction a.entries with
  | nil => exact (Rat.zero_add _).symm
  | cons x xs ih => simp only [List.cons_append, List.foldr_cons, ih, Rat.add_assoc]

/-- A tree's distribution has total weight one. -/
theorem WeightedTree.mass_toDist (t : WeightedTree α) : t.toDist.mass = 1 := by
  induction t with
  | pure a => exact Rat.add_zero 1
  | flip p h t ihh iht =>
    simp only [WeightedTree.toDist, Dist.mass_append, Dist.mass_scale, ihh, iht, Rat.mul_one]
    grind

/-- Every weight of a tree lies between zero and one. -/
def WeightedTree.Valid : WeightedTree α → Prop
  | .pure _ => True
  | .flip p h t => 0 ≤ p ∧ p ≤ 1 ∧ h.Valid ∧ t.Valid

theorem Dist.mem_scale {w : Rat} {d : Dist α} {x : α × Rat} (h : x ∈ (Dist.scale w d).entries) :
    ∃ y ∈ d.entries, x = (y.1, w * y.2) := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
  exact ⟨y, hy, rfl⟩

theorem Dist.mem_append {a b : Dist α} {x : α × Rat} (h : x ∈ (a.append b).entries) :
    x ∈ a.entries ∨ x ∈ b.entries :=
  List.mem_append.mp h

/-- A valid tree's distribution has no negative weight. -/
theorem WeightedTree.weights_nonneg {t : WeightedTree α} (hv : t.Valid) :
    ∀ x ∈ t.toDist.entries, 0 ≤ x.2 := by
  induction t with
  | pure a =>
    intro x hx
    obtain rfl := List.mem_singleton.mp hx
    grind
  | flip p h t ihh iht =>
    obtain ⟨h0, h1, hh, ht⟩ := hv
    intro x hx
    rcases Dist.mem_append hx with hx' | hx' <;> obtain ⟨y, hy, rfl⟩ := Dist.mem_scale hx'
    · exact Rat.mul_nonneg h0 (ihh hh y hy)
    · exact Rat.mul_nonneg (by grind) (iht ht y hy)

/-- The outcomes that a distribution gives with a weight other than zero. -/
def Dist.support (d : Dist α) : SetM α
  | .ok a => ∃ w, w ≠ 0 ∧ (a, w) ∈ d.entries
  | .ub _ => False

/-- A weighted tree with its weights forgotten: a tree of choices, each of
one bit. -/
def WeightedTree.forget : WeightedTree α → ChoiceTree ε α
  | .pure a => .pure a
  | .flip _ h t => .choose 1 fun b => if b = 1 then h.forget else t.forget

/-- What a distribution gives with a weight other than zero is an outcome of
the tree with its weights forgotten, in the set instance. So results about
the set of outcomes stay true of which outcomes are possible. -/
theorem WeightedTree.support_toDist {ε : Type} (t : WeightedTree α) (a : α)
    (h : t.toDist.support (.ok a)) : (t.forget : ChoiceTree ε α).toSet (.ok a) := by
  obtain ⟨w, hw, hm⟩ := h
  induction t generalizing w with
  | pure b =>
    obtain h := List.mem_singleton.mp hm
    cases h
    rfl
  | flip p l r ihl ihr =>
    rcases Dist.mem_append hm with hm' | hm' <;> obtain ⟨y, hy, hxy⟩ := Dist.mem_scale hm'
    · cases hxy
      refine ⟨1, ?_⟩
      simp only [↓reduceIte]
      exact ihl y.2 (by grind) hy
    · cases hxy
      refine ⟨0, ?_⟩
      simp only [show ¬ ((0 : BitVec 1) = 1) by decide, ↓reduceIte]
      exact ihr y.2 (by grind) hy

instance [BEq α] : BEq (Dist α) := inferInstanceAs (BEq (List (α × Rat)))

#guard (WeightedTree.toDist (.flip (1/2) (.pure 0) (.flip (1/2) (.pure 1) (.pure 2))) : Dist Nat) ==
  ([(0, 1/2), (1, 1/4), (2, 1/4)] : List (Nat × Rat))

end FirTest.G0
