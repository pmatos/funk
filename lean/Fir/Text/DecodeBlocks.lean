import Fir.Text.DecodeScope

/-!
# Decoding the blocks of a function

The second pass of decoding reads a function's blocks in the scope that the
first pass built, at any depth. A block keeps its label, and its arguments
decode as its definitions. An op's operand types are found in the scope, its
results decode as its definitions, and `decodeOp` gives its op instance from
its name, its attributes, the operand types and the result types. Its
operands, successors and location reference are kept as they are written,
and its regions decode as blocks do.

So an op of a module's tree decodes back to the op when three things hold,
which `Operation.DecodesIn` collects: in the scope, its operands have the
types of the op instance's signature (`sig`); its results have the types
that the op instance returns (`returnTypes`); and each result's type
decodes back to itself. Then `decodeOp_encode`, a law of `LawfulDialectText`,
gives the op instance. A well-formed function has all three for each of its
ops, in the scope of the first pass, since the scope gives each value the
type that `Func.typeOf` gives it.

The lemmas for blocks, ops and regions take what the decoders they call do
as hypotheses, and the last three lemmas tie them together by structural
recursion on the blocks, ops and regions, at any depth.
-/

namespace Fir.Text

variable {d : Dialect}

/-- `decode` gives `x` back from every tree that `erase` maps to `tree`. -/
def Decodes {α β γ : Type} (decode : α → Except ParseError γ) (erase : α → β) (tree : β)
    (x : γ) : Prop :=
  ∀ a, erase a = tree → decode a = .ok x

/-- The operands of an op decode as the types that the scope gives them. -/
theorem operandTypes_eq {sc : Scope d} (f : String) :
    ∀ {xs : List (Name × TextPos)} {ts : List d.Ty}, xs.map (fun x => sc[x.1]?) = ts.map some →
      operandTypes sc f xs = .ok ts
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | (x, p) :: xs, t :: ts, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [operandTypes, h.1, operandTypes_eq f h.2] <;> rfl

end Fir.Text

namespace Fir

open Text

variable {d : Dialect} [DialectText d]

/-- `decodeOps` decodes no ops as no ops. -/
theorem decodeOps_nil (sc : Scope d) (f : String) :
    Decodes (decodeOps sc f) SOp.eraseList (Operation.treeList ([] : List (Operation d))) [] := by
  intro sos h
  rw [SOp.eraseList_eq_nil h]
  simp only [decodeOps] <;> rfl

/-- `decodeBlocks` decodes no blocks as no blocks. -/
theorem decodeBlocks_nil (sc : Scope d) (f : String) :
    Decodes (decodeBlocks sc f) SBlock.eraseList (Block.treeList ([] : List (Block d))) [] := by
  intro sbs h
  rw [SBlock.eraseList_eq_nil h]
  simp only [decodeBlocks] <;> rfl

/-- `decodeBlocks` decodes a block and the blocks after it, when the types
of the block's arguments decode, `decodeOps` decodes its ops and
`decodeBlocks` the other blocks. -/
theorem decodeBlocks_cons {sc : Scope d} {f : String} {b : Block d} {bs : List (Block d)}
    (hp : ∀ y ∈ b.params, decodeTy (tyAttr y.2) = some y.2)
    (hops : Decodes (decodeOps sc f) SOp.eraseList (Operation.treeList b.body) b.body)
    (hbs : Decodes (decodeBlocks sc f) SBlock.eraseList (Block.treeList bs) bs) :
    Decodes (decodeBlocks sc f) SBlock.eraseList (Block.treeList (b :: bs)) (b :: bs) := by
  intro sbs h
  obtain ⟨⟨label, params, ops⟩, sbs', rfl, h₁, h₂, h₃, h₄⟩ := SBlock.eraseList_eq_cons h
  dsimp only at h₁ h₂ h₃
  subst h₁
  simp only [decodeBlocks, mapM_decodeDef h₂ hp, ok_bind, hops _ h₃, hbs _ h₄]
  cases b
  rfl

/-- `decodeRegions` decodes no regions as no regions. -/
theorem decodeRegions_nil (sc : Scope d) (f : String) :
    Decodes (decodeRegions sc f) SRegion.eraseList (Region.treeList ([] : List (Region d))) [] := by
  intro srs h
  rw [SRegion.eraseList_eq_nil h]
  simp only [decodeRegions] <;> rfl

/-- `decodeRegions` decodes a region and the regions after it, when
`decodeBlocks` decodes the region's blocks and `decodeRegions` the other
regions. -/
theorem decodeRegions_cons {sc : Scope d} {f : String} {r : Region d} {rs : List (Region d)}
    (hb : Decodes (decodeBlocks sc f) SBlock.eraseList (Block.treeList r.blocks) r.blocks)
    (hrs : Decodes (decodeRegions sc f) SRegion.eraseList (Region.treeList rs) rs) :
    Decodes (decodeRegions sc f) SRegion.eraseList (Region.treeList (r :: rs)) (r :: rs) := by
  intro srs h
  obtain ⟨⟨sbs⟩, srs', rfl, h₁, h₂⟩ := SRegion.eraseList_eq_cons h
  simp only [decodeRegions, hb _ h₁, ok_bind, hrs _ h₂]
  cases r
  rfl

variable [DialectSignature d]

/-- What the second pass needs of an op, in the scope `sc`: its operands
have the types of its signature, its results have the types it returns,
and each result's type decodes back to itself. -/
structure Operation.DecodesIn (sc : Scope d) (o : Operation d) : Prop where
  operands : o.operands.map (fun x => sc[x]?) = (sig o.op).map some
  results : o.results.map (·.2) = returnTypes o.op
  types : ∀ y ∈ o.results, decodeTy (tyAttr y.2) = some y.2

/-- What the second pass needs of a block, in the scope `sc`: the types of
its arguments decode back to themselves, and each of its ops decodes. -/
def Block.DecodesIn (sc : Scope d) (b : Block d) : Prop :=
  (∀ y ∈ b.params, decodeTy (tyAttr y.2) = some y.2) ∧ ∀ o ∈ b.body, o.DecodesIn sc

/-- In a scope that gives each value the type that `Func.typeOf` gives it,
each block of a well-formed function, at any depth, decodes. -/
theorem Func.WellFormed.decodesIn {f : Func d} (hf : f.WellFormed) {sc : Scope d}
    (hsc : ∀ x, sc[x]? = f.typeOf x) : ∀ b ∈ f.allBlocks, b.DecodesIn sc := by
  intro b hb
  have hdef : ∀ y ∈ b.defs, y ∈ f.defs := fun y hy =>
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨b, hb, hy⟩)
  refine ⟨fun y hy => hf.decodeTy_def (hdef y (List.mem_append_left _ hy)), fun o ho => ?_⟩
  obtain ⟨-, -, hops, hres, -, -⟩ := hf.ops o (List.mem_flatMap.mpr ⟨b, hb, ho⟩)
  refine ⟨by rw [← hops]; exact List.map_congr_left fun x _ => hsc x, hres, fun y hy => ?_⟩
  exact hf.decodeTy_def (hdef y (List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, ho, hy⟩)))

/-- `decodeOps` decodes an op and the ops after it, when the op decodes in
the scope, `decodeRegions` decodes its regions and `decodeOps` the other
ops. -/
theorem decodeOps_cons [DialectValidation d] [LawfulDialectText d] {sc : Scope d} {f : String}
    {o : Operation d} {os : List (Operation d)}
    (ho : o.DecodesIn sc)
    (hreg : Decodes (decodeRegions sc f) SRegion.eraseList (Region.treeList o.regions) o.regions)
    (hos : Decodes (decodeOps sc f) SOp.eraseList (Operation.treeList os) os) :
    Decodes (decodeOps sc f) SOp.eraseList (Operation.treeList (o :: os)) (o :: os) := by
  intro sos h
  obtain ⟨⟨results, name, namePos, attrs, operands, succs, regions, loc⟩, sos', rfl, h₁, h₂⟩ :=
    SOp.eraseList_eq_cons h
  obtain ⟨hres, hn, ha, hops, hs, hregs, hl⟩ := SOp.erase_eq_tree h₁
  dsimp only at hres hn ha hops hs hregs hl
  subst hn ha hs hl
  have hts : operandTypes sc f operands = .ok (sig o.op) := operandTypes_eq f (by
    rw [← ho.operands, ← hops, List.map_map]
    rfl)
  have hop : decodeOp (opName o.op) (opAttrs o.op) (sig o.op) (o.results.map (·.2)) =
      some o.op := by
    rw [ho.results]
    exact LawfulDialectText.decodeOp_encode o.op
  simp only [decodeOps, hts, ok_bind, mapM_decodeDef hres ho.types, hop, hreg _ hregs,
    hos _ h₂, hops]
  cases o
  rfl

mutual
/-- `decodeBlocks` decodes blocks of a module's tree back to the blocks,
when each of them, at any depth, decodes in the scope. -/
theorem Block.decodesList [DialectValidation d] [LawfulDialectText d] (sc : Scope d)
    (f : String) : ∀ bs : List (Block d),
    (∀ b ∈ Block.allBlocks bs, b.DecodesIn sc) →
    Decodes (decodeBlocks sc f) SBlock.eraseList (Block.treeList bs) bs
  | [], _ => decodeBlocks_nil sc f
  | ⟨label, params, body⟩ :: bs, h =>
    have hb : Block.DecodesIn sc ⟨label, params, body⟩ := h _ (by simp [Block.allBlocks])
    decodeBlocks_cons hb.1
      (Operation.decodesList sc f body hb.2 fun b hb' => h b (by simp [Block.allBlocks, hb']))
      (Block.decodesList sc f bs fun b hb' => h b (by simp [Block.allBlocks, hb']))

/-- `decodeOps` decodes ops of a module's tree back to the ops, when each
of them and each block of their regions, at any depth, decodes in the
scope. -/
theorem Operation.decodesList [DialectValidation d] [LawfulDialectText d] (sc : Scope d)
    (f : String) : ∀ os : List (Operation d),
    (∀ o ∈ os, o.DecodesIn sc) → (∀ b ∈ Operation.regionBlocks os, b.DecodesIn sc) →
    Decodes (decodeOps sc f) SOp.eraseList (Operation.treeList os) os
  | [], _, _ => decodeOps_nil sc f
  | ⟨results, op, operands, succs, regions, loc⟩ :: os, ho, hreg =>
    decodeOps_cons (ho _ (.head _))
      (Region.decodesList sc f regions fun b hb =>
        hreg b (by simp [Operation.regionBlocks, hb]))
      (Operation.decodesList sc f os (fun o' ho' => ho o' (.tail _ ho')) fun b hb =>
        hreg b (by simp [Operation.regionBlocks, hb]))

/-- `decodeRegions` decodes regions of a module's tree back to the regions,
when each of their blocks, at any depth, decodes in the scope. -/
theorem Region.decodesList [DialectValidation d] [LawfulDialectText d] (sc : Scope d)
    (f : String) : ∀ rs : List (Region d),
    (∀ b ∈ Region.allBlocks rs, b.DecodesIn sc) →
    Decodes (decodeRegions sc f) SRegion.eraseList (Region.treeList rs) rs
  | [], _ => decodeRegions_nil sc f
  | ⟨blocks⟩ :: rs, h =>
    decodeRegions_cons
      (Block.decodesList sc f blocks fun b hb => h b (by simp [Region.allBlocks, hb]))
      (Region.decodesList sc f rs fun b hb => h b (by simp [Region.allBlocks, hb]))
end

end Fir
