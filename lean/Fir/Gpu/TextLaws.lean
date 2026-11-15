import Fir.Gpu.Validation
import Fir.Core.Names
import Fir.Core.TextLaws
import Fir.Sum.TextLaws
import Fir.Text.PrintParse

/-!
The text of `gpu` is lawful, and so is the text of the sum of the core and
`gpu` (ADR-2026-11-09-1545). Each op of `gpu` decodes from its own name,
dimension and result type, and from nothing else, and each word of `gpu`
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

/-- Every op of `gpu` decodes from its name and attributes, at its operand
and result types. -/
theorem Op.decode_encode (o : Op) : Op.decode o.name o.attrs o.sig o.returnTypes = some o := by
  cases o with
  | query q d w => simp [Op.decode, Op.name, Op.attrs, Op.sig, Op.returnTypes,
      Query.decode_name, Dim.decode_word]

/-- An op of `gpu` decodes only from its own name, attributes, operand
types and result types. -/
theorem Op.encode_decode {n : String} {as : List Attr} {ts rs : List (Core.Ty ⊕ Empty)} {o : Op}
    (h : Op.decode n as ts rs = some o) :
    o.name = n ∧ o.attrs = as ∧ o.sig = ts ∧ o.returnTypes = rs := by
  unfold Op.decode at h
  split at h
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
  opName_isWord | .query q .. => by change isWord q.name = true; cases q <;> decide
  opAttrs_writable | .query _ d _ => ⟨by change isWord d.word = true; cases d <;> decide, trivial⟩
  tyAttr_isType := attr_isType

instance instLawfulDialectText : LawfulDialectText GpuDialect := lawfulDialectText

/-- The words of a dimension's attribute name `gpu` alone. -/
theorem dialectsAll_attrs (o : Op) : Attr.dialectsAll (Op.attrs o) = ["gpu"] := by
  cases o with
  | query _ d _ => cases d <;> rfl

/-- `gpu` writes each op and each dimension under its name, and has no type
of its own. -/
instance lawfulDialectName : LawfulDialectName CoreDialect GpuExt where
  opName_named
    | .query q .. => show wordDialect q.name = some "gpu" by cases q <;> decide
  opAttrs_mem o x h := by
    rw [show opAttrs (d := GpuDialect) o = Op.attrs o from rfl, dialectsAll_attrs] at h
    simp only [List.mem_singleton] at h
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
