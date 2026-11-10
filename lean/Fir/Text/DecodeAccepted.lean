import Fir.Text.DecodeAcceptedScope

/-!
# The second pass accepts what can be written

The second pass of decoding decodes each block and op of a function in the
scope that the first pass built. On a tree that can be written, it gives
blocks and ops that the scope accepts: what a well-formed function asks of
each op, with the scope in place of the type that the function gives each
value, and definitions that can be written and decode back to themselves.

Two laws of a lawful text turn what decoding read into what it gives. The
first says that a type that decodes from an attribute is written as that
attribute, so a type written as a type decodes back to itself. The second
says that the op instance that the dialect decodes from a name, attributes,
operand types and result types has that name, those attributes and those
types. Its name and attributes came from the tree, so they can be written;
its operand types came from the scope; and its result types are those of
the op's results.

As for the first pass, the lemmas for blocks, ops and regions take what the
pass does with the parts they hold as hypotheses, and three short theorems,
proved together by recursion on the tree, tie them together.
-/

namespace Fir.Text

variable {d : Dialect}

/-- A definition can be written and read back: its value's name is a name,
and its type is written as a type and decodes back to itself. -/
def WritableDef [DialectText d] (y : Name × d.Ty) : Prop :=
  isName y.1 ∧ (tyAttr y.2).IsType ∧ decodeTy (tyAttr y.2) = some y.2

/-- The types that `operandTypes` gives are the ones that the scope gives
the operands. -/
theorem operandTypes_ok {sc : Scope d} {g : String} :
    ∀ {xs : List (Name × TextPos)} {ts : List d.Ty}, operandTypes sc g xs = .ok ts →
      xs.map (fun x => sc[x.1]?) = ts.map some
  | [], ts, h => by
    rw [operandTypes] at h
    cases h
    rfl
  | (x, p) :: xs, ts, h => by
    rw [operandTypes] at h
    split at h
    · rename_i t ht
      bind_step h with ⟨ts', h₁, h⟩
      cases h
      simp [ht, operandTypes_ok h₁]
    · cases h

end Fir.Text

namespace Fir

open Text

variable {d : Dialect} [DialectSignature d] [DialectText d]

/-! # Blocks and ops that a scope accepts -/

/-- What the second pass gives of an op, in the scope `sc`: what
`Func.OpWellFormed` asks, with the scope in place of `Func.typeOf`, results
that can be written and read back, and regions whose kinds are words. -/
structure Operation.AcceptedIn (sc : Scope d) (o : Operation d) : Prop where
  name : isWord (opName o.op)
  attrs : Attr.AllWritable (opAttrs o.op)
  operands : o.operands.map (fun x => sc[x]?) = (sig o.op).map some
  results : o.results.map (·.2) = returnTypes o.op
  succs : ∀ s ∈ o.succs, s.Writable
  loc : o.loc < Location.limit
  defs : ∀ y ∈ o.results, WritableDef y
  kinds : ∀ r ∈ o.regions, ∀ k ∈ r.kind, isWord k

/-- What the second pass gives of a block, in the scope `sc`: its label is
a name, its arguments can be written and read back, and so can each of its
ops. -/
structure Block.AcceptedIn (sc : Scope d) (b : Block d) : Prop where
  label : isName b.label
  params : ∀ y ∈ b.params, WritableDef y
  ops : ∀ o ∈ b.body, o.AcceptedIn sc

/-- Each block of `bs`, at any depth, is accepted in the scope `sc`. -/
def Block.AllAcceptedIn (sc : Scope d) (bs : List (Block d)) : Prop :=
  ∀ b ∈ Block.allBlocks bs, b.AcceptedIn sc

/-- Each op of `os`, and each block of their regions at any depth, is
accepted in the scope `sc`. -/
def Operation.AllAcceptedIn (sc : Scope d) (os : List (Operation d)) : Prop :=
  (∀ o ∈ os, o.AcceptedIn sc) ∧ ∀ b ∈ Operation.regionBlocks os, b.AcceptedIn sc

/-- Each of the regions `rs` names its kind, if any, by a word, and each of
their blocks, at any depth, is accepted in the scope `sc`. -/
def Region.AllAcceptedIn (sc : Scope d) (rs : List (Region d)) : Prop :=
  (∀ r ∈ rs, ∀ k ∈ r.kind, isWord k) ∧ ∀ b ∈ Region.allBlocks rs, b.AcceptedIn sc

end Fir

namespace Fir.Text

variable {d : Dialect} [DialectSignature d] [DialectText d]

/-! # The second pass, part by part -/

/-- A type that decodes from an attribute written as a type is written as
that attribute, and decodes back to itself. -/
theorem decodeType_writable [DialectValidation d] [LawfulDialectText d] {a : Attr}
    {p : TextPos} {t : d.Ty} (h : decodeType a p = .ok t) (ha : a.IsType) :
    (tyAttr t).IsType ∧ decodeTy (tyAttr t) = some t := by
  unfold decodeType at h
  split at h
  · rename_i t' ht
    cases h
    rw [LawfulDialectText.encode_decodeTy _ _ ht]
    exact ⟨ha, ht⟩
  · cases h

/-- A definition that can be written decodes as one that can be written and
read back. -/
theorem decodeDef_writable [DialectValidation d] [LawfulDialectText d] {x : SDef}
    {y : Name × d.Ty} (h : decodeDef x = .ok y) (hx : x.Writable) : WritableDef y := by
  unfold decodeDef at h
  bind_step h with ⟨t, ht, h⟩
  cases h
  exact ⟨hx.1, decodeType_writable ht hx.2⟩

/-- Definitions that can be written decode as ones that can be written and
read back. -/
theorem mapM_decodeDef_writable [DialectValidation d] [LawfulDialectText d] :
    ∀ {xs : List SDef} {ys : List (Name × d.Ty)},
      xs.mapM decodeDef = .ok ys → (∀ x ∈ xs, x.Writable) → ∀ y ∈ ys, WritableDef y
  | [], ys, h, _ => by cases h; simp
  | x :: xs, ys, h, hw => by
    rw [List.mapM_cons] at h
    bind_step h with ⟨y, h₁, h⟩
    bind_step h with ⟨ys', h₂, h⟩
    cases h
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact decodeDef_writable h₁ (hw x (.head _))
    · exact mapM_decodeDef_writable h₂ (fun x' hx' => hw x' (.tail _ hx')) z hz

/-- On a part of a tree that `W` holds of, `decode` gives what `P` holds
of. -/
def DecodesTo {α β : Type} (decode : α → Except ParseError β) (W : α → Prop) (P : β → Prop)
    (a : α) : Prop :=
  W a → ∀ x, decode a = .ok x → P x

/-- The second pass decodes no blocks as no blocks. -/
theorem decodes_blocks_nil (sc : Scope d) (g : String) :
    DecodesTo (decodeBlocks sc g) SBlock.WritableList (Block.AllAcceptedIn sc) [] := by
  intro _ x h
  rw [decodeBlocks] at h
  cases h
  simp [Block.AllAcceptedIn, Block.allBlocks]

/-- The second pass accepts a block, the blocks of the regions of its ops
and the blocks after it, when it accepts the ops and the blocks after it. -/
theorem decodes_blocks_cons [DialectValidation d] [LawfulDialectText d] {sc : Scope d}
    {g : String} {label : Name} {params : List SDef} {ops : List SOp} {sbs : List SBlock}
    (hops : DecodesTo (decodeOps sc g) SOp.WritableList (Operation.AllAcceptedIn sc) ops)
    (hbs : DecodesTo (decodeBlocks sc g) SBlock.WritableList (Block.AllAcceptedIn sc) sbs) :
    DecodesTo (decodeBlocks sc g) SBlock.WritableList (Block.AllAcceptedIn sc)
      (⟨label, params, ops⟩ :: sbs) := by
  intro hw x h
  simp only [SBlock.WritableList] at hw
  obtain ⟨hl, hp, hw₁, hw₂⟩ := hw
  rw [decodeBlocks] at h
  bind_step h with ⟨ps, f₁, h⟩
  bind_step h with ⟨os, f₂, h⟩
  bind_step h with ⟨bs, f₃, h⟩
  cases h
  obtain ⟨k₁, k₂⟩ := hops hw₁ os f₂
  have k₃ := hbs hw₂ bs f₃
  intro b hb
  simp only [Block.allBlocks, List.cons_append, List.mem_cons, List.mem_append] at hb
  rcases hb with rfl | hb | hb
  · exact ⟨hl, mapM_decodeDef_writable f₁ hp, k₁⟩
  · exact k₂ b hb
  · exact k₃ b hb

/-- The second pass decodes no ops as no ops. -/
theorem decodes_ops_nil (sc : Scope d) (g : String) :
    DecodesTo (decodeOps sc g) SOp.WritableList (Operation.AllAcceptedIn sc) [] := by
  intro _ x h
  rw [decodeOps] at h
  cases h
  simp [Operation.AllAcceptedIn, Operation.regionBlocks]

/-- The second pass accepts an op, when it accepts the blocks of the op's
regions and the ops after it. `encode_decodeOp` gives back the name, the
attributes, the operand types and the result types that `decodeOp` was
given. -/
theorem decodes_ops_cons [DialectValidation d] [LawfulDialectText d] {sc : Scope d}
    {g : String} {results : List SDef} {name : String} {namePos : TextPos} {attrs : List Attr}
    {operands : List (Name × TextPos)} {succs : List Succ} {regions : List SRegion}
    {loc : LocRef} {sos : List SOp}
    (hreg : DecodesTo (decodeRegions sc g) SRegion.WritableList (Region.AllAcceptedIn sc)
      regions)
    (hos : DecodesTo (decodeOps sc g) SOp.WritableList (Operation.AllAcceptedIn sc) sos) :
    DecodesTo (decodeOps sc g) SOp.WritableList (Operation.AllAcceptedIn sc)
      (⟨results, name, namePos, attrs, operands, succs, regions, loc⟩ :: sos) := by
  intro hw x h
  simp only [SOp.WritableList, SOp.Writable] at hw
  obtain ⟨⟨hres, hname, hattrs, hsuccs, hregs, hloc⟩, hw₂⟩ := hw
  rw [decodeOps] at h
  bind_step h with ⟨ts, f₁, h⟩
  bind_step h with ⟨rs, f₂, h⟩
  split at h
  · cases h
  rename_i op hop
  bind_step h with ⟨regs, f₃, h⟩
  bind_step h with ⟨os, f₄, h⟩
  cases h
  obtain ⟨e₁, e₂, e₃, e₄⟩ := LawfulDialectText.encode_decodeOp _ _ _ _ _ hop
  have k₁ := hreg hregs regs f₃
  obtain ⟨k₂, k₃⟩ := hos hw₂ os f₄
  refine ⟨fun o ho => ?_, fun b hb => ?_⟩
  · rcases List.mem_cons.mp ho with rfl | ho
    · refine ⟨e₁ ▸ hname, e₂ ▸ hattrs, ?_, e₄.symm, hsuccs, hloc,
        mapM_decodeDef_writable f₂ hres, k₁.1⟩
      rw [e₃, ← operandTypes_ok f₁, List.map_map]
      rfl
    · exact k₂ o ho
  · simp only [Operation.regionBlocks, List.mem_append] at hb
    rcases hb with hb | hb
    · exact k₁.2 b hb
    · exact k₃ b hb

/-- The second pass decodes no regions as no regions. -/
theorem decodes_regions_nil (sc : Scope d) (g : String) :
    DecodesTo (decodeRegions sc g) SRegion.WritableList (Region.AllAcceptedIn sc) [] := by
  intro _ x h
  rw [decodeRegions] at h
  cases h
  simp [Region.AllAcceptedIn, Region.allBlocks]

/-- The second pass accepts the blocks of regions, when it accepts each
region's blocks and the regions after it. -/
theorem decodes_regions_cons {sc : Scope d} {g : String} {k : Option Name} {bs : List SBlock}
    {srs : List SRegion}
    (hb : DecodesTo (decodeBlocks sc g) SBlock.WritableList (Block.AllAcceptedIn sc) bs)
    (hrs : DecodesTo (decodeRegions sc g) SRegion.WritableList (Region.AllAcceptedIn sc) srs) :
    DecodesTo (decodeRegions sc g) SRegion.WritableList (Region.AllAcceptedIn sc)
      (⟨k, bs⟩ :: srs) := by
  intro hw x h
  simp only [SRegion.WritableList] at hw
  rw [decodeRegions] at h
  bind_step h with ⟨blocks, f₁, h⟩
  bind_step h with ⟨rs, f₂, h⟩
  cases h
  have k₁ := hb hw.2.1 blocks f₁
  have k₂ := hrs hw.2.2 rs f₂
  refine ⟨fun r hr => ?_, fun b hb => ?_⟩
  · rcases List.mem_cons.mp hr with rfl | hr
    · exact hw.1
    · exact k₂.1 r hr
  · simp only [Region.allBlocks, List.mem_append] at hb
    rcases hb with hb | hb
    · exact k₁ b hb
    · exact k₂.2 b hb

mutual
/-- The second pass over blocks, at any depth. -/
theorem SBlock.decodesTo [DialectValidation d] [LawfulDialectText d] (sc : Scope d)
    (g : String) : ∀ sbs : List SBlock,
      DecodesTo (decodeBlocks sc g) SBlock.WritableList (Block.AllAcceptedIn sc) sbs
  | [] => decodes_blocks_nil sc g
  | ⟨_, _, ops⟩ :: sbs => decodes_blocks_cons (SOp.decodesTo sc g ops) (SBlock.decodesTo sc g sbs)

/-- The second pass over ops, at any depth. -/
theorem SOp.decodesTo [DialectValidation d] [LawfulDialectText d] (sc : Scope d)
    (g : String) : ∀ sos : List SOp,
      DecodesTo (decodeOps sc g) SOp.WritableList (Operation.AllAcceptedIn sc) sos
  | [] => decodes_ops_nil sc g
  | ⟨_, _, _, _, _, _, regions, _⟩ :: sos =>
    decodes_ops_cons (SRegion.decodesTo sc g regions) (SOp.decodesTo sc g sos)

/-- The second pass over regions, at any depth. -/
theorem SRegion.decodesTo [DialectValidation d] [LawfulDialectText d] (sc : Scope d)
    (g : String) : ∀ srs : List SRegion,
      DecodesTo (decodeRegions sc g) SRegion.WritableList (Region.AllAcceptedIn sc) srs
  | [] => decodes_regions_nil sc g
  | ⟨_, bs⟩ :: srs => decodes_regions_cons (SBlock.decodesTo sc g bs) (SRegion.decodesTo sc g srs)
end

end Fir.Text
