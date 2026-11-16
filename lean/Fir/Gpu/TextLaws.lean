import Fir.Gpu.Validation
import Fir.Core.Names
import Fir.Core.TextLaws
import Fir.Core.AllocaTextLaws
import Fir.Sum.TextLaws
import Fir.Text.PrintParse

/-!
The text of `gpu` is lawful, and so is the text of the sum of the core and
`gpu` (ADR-2026-11-09-1545). Each question of `gpu` decodes from its own
name, dimension and result type, and each allocation from its own name, its
attributes and its result type, as `alloca` does after its kind, and from
nothing else, and each word of `gpu`
is written under its name. The sum's text is then lawful with no new
assumption (`Dialect.sum.lawful_of_names`), so the round trip holds for
every well-formed module of the sum, a host module with a device module
included, and every valid module of the sum is well formed.
-/

namespace Fir.Gpu

/-- A question's name decodes to it. -/
theorem Query.decode_name (q : Query) : Query.decode q.name = some q := by
  cases q <;> rfl

/-- A name decodes only to the question it names. -/
theorem Query.name_decode {n : String} {q : Query} (h : Query.decode n = some q) : q.name = n := by
  unfold Query.decode at h
  split at h <;> cases h <;> rfl

/-- A dimension's word decodes to it. -/
theorem Dim.decode_word (d : Dim) : Dim.decode d.word = some d := by
  cases d <;> rfl

/-- A word decodes only to the dimension it names. -/
theorem Dim.word_decode {w : String} {d : Dim} (h : Dim.decode w = some d) : d.word = w := by
  unfold Dim.decode at h
  split at h <;> cases h <;> rfl

/-- No question is named as the allocation. -/
theorem Query.name_ne (q : Query) : q.name ≠ allocName := by
  cases q <;> decide

/-- An allocation reads back from its attributes: `alloca`'s, with the kind
`global` before them, read back as `alloca`. -/
theorem decodeAlloc_attrs (t : Core.Ty) (c : Nat) (a : Option Nat) (n : Nat) :
    decodeAlloc (Op.alloc t c a n).attrs n = some (.alloc t c a n) := by
  unfold decodeAlloc
  rw [show Attr.word Memory.AllocKind.global.word :: (Op.alloc t c a n).attrs =
    Core.allocaAttrs .global t c a from rfl, Core.decodeAlloca_allocaAttrs]

/-- Every op of `gpu` decodes from its name and attributes, at its operand
and result types. -/
theorem Op.decode_encode (o : Op) : Op.decode o.name o.attrs o.sig o.returnTypes = some o := by
  cases o with
  | query q d w => simp [Op.decode, Op.name, Op.attrs, Op.sig, Op.returnTypes,
      Query.decode_name, Dim.decode_word, Query.name_ne]
  | alloc t c a n =>
    simp only [Op.decode, Op.name, Op.sig, Op.returnTypes, ite_true]
    exact decodeAlloc_attrs t c a n

/-- An allocation decodes only from its own attributes and a pointer result
of its memory. -/
theorem decodeAlloc_eq {as : List Attr} {m : Nat} {o : Op} (h : decodeAlloc as m = some o) :
    o.attrs = as ∧ o.returnTypes = [.inl (.ptr m)] ∧ o.name = allocName ∧ o.sig = [] := by
  unfold decodeAlloc at h
  split at h
  · rename_i k t c a m' heq
    cases h
    obtain ⟨-, ha, -, hr⟩ := Core.decodeAlloca_eq heq
    have hm : m' = m := by cases hr; rfl
    subst hm
    exact ⟨congrArg List.tail ha, rfl, rfl, rfl⟩
  · cases h

/-- An op of `gpu` decodes only from its own name, attributes, operand
types and result types. -/
theorem Op.encode_decode {n : String} {as : List Attr} {ts rs : List (Core.Ty ⊕ Empty)} {o : Op}
    (h : Op.decode n as ts rs = some o) :
    o.name = n ∧ o.attrs = as ∧ o.sig = ts ∧ o.returnTypes = rs := by
  unfold Op.decode at h
  split at h
  · rename_i hn
    subst hn
    split at h
    · obtain ⟨ha, hr, hn, hs⟩ := decodeAlloc_eq h
      exact ⟨hn, ha, hs, hr⟩
    · cases h
  · split at h
    · rename_i q w r hq
      obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨Query.name_decode hq, by simp [Op.attrs, Dim.word_decode hd], rfl, rfl⟩
    · cases h

/-- `gpu` reads back each valid type it writes: the core's. -/
theorem decodeTy_attr (t : Core.Ty ⊕ Empty) (h : ValidTy t) : decodeTy (tyAttr t) = some t := by
  cases t with
  | inl t => simp [decodeTy, tyAttr, Core.Ty.decode_attr t h]
  | inr e => exact e.elim

/-- A type that `gpu` reads is written as it was read. -/
theorem attr_decodeTy {a : Attr} {t : Core.Ty ⊕ Empty} (h : decodeTy a = some t) :
    tyAttr t = a := by
  obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp h
  exact Core.Ty.attr_decode ht'

/-- Every valid type of `gpu` is written as a type. -/
theorem attr_isType (t : Core.Ty ⊕ Empty) (h : ValidTy t) : (tyAttr t).IsType := by
  cases t with
  | inl t => exact Core.Ty.attr_isType t h
  | inr e => exact e.elim

/-- The text of `gpu` meets the seven laws. -/
theorem lawfulDialectText : LawfulDialectText GpuDialect where
  decodeOp_encode := Op.decode_encode
  encode_decodeOp _ _ _ _ _ h := Op.encode_decode h
  decodeTy_encode := decodeTy_attr
  encode_decodeTy _ _ h := attr_decodeTy h
  opName_isWord
    | .query q .. => by change isWord q.name = true; cases q <;> decide
    | .alloc .. => by change isWord allocName = true; decide
  opAttrs_writable
    | .query _ d _ => ⟨by change isWord d.word = true; cases d <;> decide, trivial⟩
    | .alloc t c a _ => (Core.allocaAttrs_writable .global t c a).2
  tyAttr_isType := attr_isType

instance instLawfulDialectText : LawfulDialectText GpuDialect := lawfulDialectText

/-- The words of a dimension's attribute name `gpu` alone, and an
allocation's attributes, the core's, name no dialect. -/
theorem dialectsAll_attrs (o : Op) : Attr.dialectsAll (Op.attrs o) ⊆ ["gpu"] := by
  cases o with
  | query _ d _ => cases d <;> exact List.Subset.refl _
  | alloc t c a n =>
    have h := Core.opAttrs_bare (.alloca .global t c a n)
    change Attr.dialectsAll (.word Memory.AllocKind.global.word :: (Op.alloc t c a n).attrs) = [] at h
    simp only [Attr.dialectsAll, List.append_eq_nil_iff] at h
    rw [h.2]
    exact List.nil_subset _

/-- `gpu` writes each op and each dimension under its name, and has no type
of its own. -/
instance lawfulDialectName : LawfulDialectName CoreDialect GpuExt where
  opName_named
    | .query q .. => show wordDialect q.name = some "gpu" by cases q <;> decide
    | .alloc .. => show wordDialect allocName = some "gpu" by decide
  opAttrs_mem o x h := by
    rw [show opAttrs (d := GpuDialect) o = Op.attrs o from rfl] at h
    have h := List.mem_singleton.1 (dialectsAll_attrs o h)
    subst h
    exact List.mem_append_right _ (List.mem_singleton_self _)
  tyAttr_named t := t.elim
  tyAttr_mem t := t.elim
  kind_named _ h := nomatch h

end Fir.Gpu

namespace Fir

/-- `gpu`'s name is new to the core. -/
theorem Gpu.name_new : name GpuExt ∉ names CoreDialect := Core.name_new _

/-- The text of the sum of the core and `gpu` is lawful. -/
instance Gpu.instLawfulDialectTextSum : LawfulDialectText CoreGpu := Dialect.sum.lawful_of_names Gpu.name_new

/-- Every valid module of the sum of the core and `gpu` is well formed. -/
theorem Gpu.validIsWellFormed : ValidIsWellFormed (d := CoreGpu) :=
  Dialect.sum.validIsWellFormed Gpu.name_new

/-- `parse(print(m)) == m` for every well-formed module of the sum of the
core and `gpu`. -/
theorem Gpu.printThenParse : PrintThenParse (d := CoreGpu) Fir.parse :=
  Fir.printThenParse

/-- `print(parse(t)) == t` for every text printed from a well-formed module
of the sum of the core and `gpu`. -/
theorem Gpu.parseThenPrint : ParseThenPrint (d := CoreGpu) Fir.parse :=
  Fir.parseThenPrint

/-- Two valid modules of the sum of the core and `gpu` that print the same
text are the same module. -/
theorem Gpu.print_injective {m₁ m₂ : Module CoreGpu} (h₁ : m₁.Valid) (h₂ : m₂.Valid)
    (he : m₁.print = m₂.print) : m₁ = m₂ :=
  h₁.print_injective h₂ he

end Fir
