import Fir

/-!
Proofs that the spec's example module is valid, for the tests of the
theorems on progress and no stuck path: their hypotheses hold of real
functions with loops.

The validation check decides validity, but its proof cannot run in the
kernel: it looks up labels in `Std.HashMap` and `Std.HashSet`, which
`decide +kernel` cannot reduce even with `Nat` keys, and `String.hash` is
opaque. So these proofs go rule by rule, and the kernel decides most of
them. Scope is decided against a list of facts of dominance, each proved
by hand (`ScopeOK`, `opValid_of`), and reachability is a path from the
entry to each block, given by hand.
`FirTest.RunsLoops` uses the same tests for a function of its own.
-/

namespace FirTest

open Fir Core Example

section

variable {d : Dialect}

/-- A use of `x` by the op at index `i` of the block labelled `l` is in
scope, as a decidable test: `x` is defined, and each block that defines it
dominates the use, by being `l` or by the list `dom` of dominance facts. -/
def ScopeOK (f : Func d) (dom : List (Name × Name)) (x l : Name) (i : Nat) : Prop :=
  (x ∈ f.params.map (·.1) ∨ ∃ b ∈ f.blocks,
      x ∈ b.params.map (·.1) ∨ ∃ o ∈ b.body, x ∈ o.results.map (·.1)) ∧
    (∀ b ∈ f.blocks, x ∈ b.params.map (·.1) → b.label = l ∨ (b.label, l) ∈ dom) ∧
    ∀ b ∈ f.blocks, ∀ (j : Nat) (hj : j < b.body.length), x ∈ b.body[j].results.map (·.1) →
      (b.label = l ∧ j < i) ∨ (b.label ≠ l ∧ (b.label, l) ∈ dom)

instance (f : Func d) (dom : List (Name × Name)) (x l : Name) (i : Nat) :
    Decidable (ScopeOK f dom x l i) := by
  unfold ScopeOK
  exact @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance inferInstance)

/-- The test of scope is sound, given true facts of dominance. -/
theorem ScopeOK.inScope {f : Func d} {dom : List (Name × Name)}
    (hdom : ∀ p ∈ dom, f.Dominates p.1 p.2) {x l : Name} {i : Nat}
    (h : ScopeOK f dom x l i) : f.InScope x l i := by
  obtain ⟨hdef, hargs, hres⟩ := h
  refine ⟨?_, fun s hs => ?_⟩
  · rcases hdef with hp | ⟨b, hb, hx | ⟨o, ho, hx⟩⟩
    · exact ⟨.param, hp⟩
    · exact ⟨.arg b.label, b, hb, rfl, hx⟩
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ho
      exact ⟨.result b.label j, b, hb, rfl, _, List.getElem?_eq_getElem hj, hx⟩
  · cases s with
    | param => trivial
    | arg a =>
      obtain ⟨b, hb, rfl, hx⟩ := hs
      rcases hargs b hb hx with h | h
      · exact .inl h
      · exact hdom _ h
    | result a j =>
      obtain ⟨b, hb, rfl, o, ho, hx⟩ := hs
      obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 ho
      rcases hres b hb j hj hx with h | ⟨hne, h⟩
      · exact .inl h
      · exact .inr ⟨hne, hdom _ h⟩

end

/-- The rules of an op of a core function, as a decidable test: scope
against the dominance facts `dom`, a successor's block found by its
label. -/
def OpOK (ctx : ModuleContext CoreDialect) (f : Func CoreDialect) (dom : List (Name × Name))
    (b : Block CoreDialect) (i : Nat) (o : Operation CoreDialect) : Prop :=
  o.regions.isEmpty = true ∧
  o.operands.map f.typeOf = (sig o.op).map some ∧
  o.results.map (·.2) = returnTypes o.op ∧
  (isTerminator o.op = true ↔ i + 1 = b.body.length) ∧
  o.succs.length = succCount o.op ∧
  (isTerminator o.op = false → o.succs = []) ∧
  (∀ s ∈ o.succs, f.entryLabel? ≠ some s.label ∧
    ∃ tgt ∈ (f.block? s.label).toList, s.args.map f.typeOf = tgt.params.map (some ·.2)) ∧
  (∀ x ∈ o.uses, ScopeOK f dom x b.label i) ∧
  (∀ g ∈ symbolRefs o.op, (ctx.symbols g).isSome) ∧
  validOp ⟨ctx.symbols, f.results⟩ o.op ∧
  o.loc ∈ ctx.locKeys

instance (ctx : ModuleContext CoreDialect) (f : Func CoreDialect) (dom : List (Name × Name))
    (b : Block CoreDialect) (i : Nat) (o : Operation CoreDialect) :
    Decidable (OpOK ctx f dom b i o) := by
  unfold OpOK
  repeat (first | exact inferInstance | refine @instDecidableAnd _ _ inferInstance ?_)

/-- Each op of a core function that passes the test is valid. -/
theorem opValid_of {ctx : ModuleContext CoreDialect} {f : Func CoreDialect}
    {dom : List (Name × Name)} (hdom : ∀ p ∈ dom, f.Dominates p.1 p.2)
    (h : ∀ b ∈ f.blocks, ∀ (i : Nat) (hi : i < b.body.length), OpOK ctx f dom b i b.body[i]) :
    ∀ b ∈ f.blocks, ∀ (i : Nat) (o : Operation CoreDialect), b.body[i]? = some o →
      f.OpValid ctx b i o := by
  intro b hb i o ho
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 ho
  obtain ⟨hreg, hoty, hrty, hterm, hcount, hnone, hsucc, hscope, hsym, hop, hloc⟩ := h b hb i hi
  refine ⟨List.isEmpty_iff.1 hreg, hoty, hrty, hterm, hcount, hnone, fun s hs => ?_,
    fun x hx => (hscope x hx).inScope hdom, hsym, hop, hloc⟩
  obtain ⟨hne, tgt, htgt, hty⟩ := hsucc s hs
  exact ⟨hne, tgt, Option.mem_toList.1 htgt, hty⟩

/-! # `@sum`

`^loop` dominates `^body`: the entry jumps only to `^loop`, so no path
from the entry reaches `^body` without passing through `^loop`. Every
other use in `@sum` is of a parameter, of an argument of its own block,
or of a result of an earlier op of its own block. -/

/-- `@sum`'s edges, from each block to the blocks it jumps to. -/
theorem sum_edge {a l : Name} (h : sum.Edge a l) :
    (a = "entry" ∧ l = "loop") ∨ (a = "loop" ∧ (l = "exit" ∨ l = "body")) ∨
      (a = "body" ∧ l = "loop") := by
  obtain ⟨blk, hb, rfl, hl⟩ := h
  simp only [sum, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;>
    simp_all [Block.succLabels, op]

/-- `^loop` dominates `^body`. -/
theorem sum_loop_dominates_body : sum.Dominates "loop" "body" := by
  refine .inr fun h => ?_
  have hentry : ∀ y, sum.ReachesAvoiding "loop" y → y = "entry" := by
    intro y hy
    induction hy with
    | entry he _ => simpa [Func.entryLabel?, sum, Func.blocks] using he.symm
    | step _ he hne ih =>
      subst ih
      rcases sum_edge he with ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact absurd rfl hne
      · exact absurd h (by decide)
      · exact absurd h (by decide)
  exact absurd (hentry _ h) (by decide)

/-- The edges of `@sum` that reach each of its blocks. -/
theorem sum_reachable : ∀ b ∈ sum.blocks, sum.Reachable b.label := by
  have hentry : sum.Reachable "entry" := .entry rfl
  have hloop : sum.Reachable "loop" :=
    .step hentry ⟨_, List.mem_cons_self, rfl, by decide⟩
  have hbody : sum.Reachable "body" :=
    .step hloop ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl, by decide⟩
  have hexit : sum.Reachable "exit" :=
    .step hloop ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl, by decide⟩
  intro b hb
  simp only [sum, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> assumption

/-- `@sum` is valid in its module. -/
theorem sum_valid : sum.Valid sumModule.context where
  bodyKind := rfl
  entry := ⟨_, rfl, rfl⟩
  reachable := sum_reachable
  labelsUnique := by decide
  namesUnique := by decide +kernel
  names x hx := Text.isName_iff.2 (by revert x; decide +kernel)
  labels b hb := Text.isName_iff.2 (by revert b; decide +kernel)
  types t ht := by revert t; decide +kernel
  blocksNonEmpty b hb := by
    simp only [sum, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> simp [op]
  ops := opValid_of (dom := [("loop", "body")])
    (by simpa using sum_loop_dominates_body) (by decide +kernel)
  dialect := trivial

/-! # `@sum10` and the module -/

/-- `@sum10` is valid in its module: it has one block, and its `call`
names `@sum` at `@sum`'s type. -/
theorem sum10_valid : sum10.Valid sumModule.context where
  bodyKind := rfl
  entry := ⟨_, rfl, rfl⟩
  reachable b hb := by
    simp only [sum10, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    exact .entry rfl
  labelsUnique := by decide
  namesUnique := by decide +kernel
  names x hx := Text.isName_iff.2 (by revert x; decide +kernel)
  labels b hb := Text.isName_iff.2 (by revert b; decide +kernel)
  types t ht := by revert t; decide +kernel
  blocksNonEmpty b hb := by
    simp only [sum10, Func.blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    simp [op]
  ops := opValid_of (dom := []) (fun _ h => nomatch h) (by decide +kernel)
  dialect := trivial

/-- The spec's example module is valid. -/
theorem sumModule_valid : sumModule.Valid where
  symbolsUnique := by decide
  flat i hi := by
    simp only [sumModule, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> rfl
  locs := by
    refine ⟨by decide, by unfold LocTable.InLimits; decide +kernel, fun e he => ?_⟩
    simp only [sumModule, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Location.WellFormed, Location.refs]
  funcs f hf := by
    simp only [sumModule, Module.funcs, List.filterMap_cons, Item.func?, List.filterMap_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact sum_valid
    · exact sum10_valid
  dialectNames := by simp [sumModule]
  dialectsUnique := by simp [sumModule]

end FirTest
