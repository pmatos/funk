import Fir.Text.DecodeAccepted

/-!
# Functions, items and the module as decoded

`decodeFunc` joins the two passes. The first pass names each value once,
and its scope gives each value the type that `Func.typeOf` gives it, since
the scope's definitions are a permutation of `Func.defs`. So the scope can
be replaced by `Func.typeOf` in what the second pass accepts, and each
decoded function is well formed (`decodeFunc_wellFormed`). Its result types
decode as types do, from attributes written as types.

`decodeItem` decodes only a `func` with no attributes, whose body holds
blocks or holds nothing, and `decodeModule` keeps the location table as it
was read. So a module decoded from a tree that can be written is well
formed: the decoding step, `decodeModule_wellFormed`.
-/

namespace Fir

open Text

variable {d : Dialect} [DialectSignature d] [DialectValidation d] [DialectText d]
  [LawfulDialectText d]


/-- Result types that decode, from types written as types, can be written
and decode back to themselves. -/
theorem mapM_decodeType_writable {g : Attr × TextPos → Except ParseError d.Ty}
    (hg : ∀ a p, g (a, p) = decodeType a p) :
    ∀ {as : List (Attr × TextPos)} {ts : List d.Ty}, as.mapM g = .ok ts →
      (∀ a ∈ as, a.1.IsType) → ∀ t ∈ ts, (tyAttr t).IsType ∧ decodeTy (tyAttr t) = some t
  | [], ts, h, _ => by cases h; simp
  | (a, p) :: as, ts, h, hw => by
    rw [List.mapM_cons] at h
    bind_step h with ⟨t, h₁, h⟩
    bind_step h with ⟨ts', h₂, h⟩
    cases h
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact decodeType_writable ((hg a p).symm.trans h₁) (hw _ (.head _))
    · exact mapM_decodeType_writable hg h₂ (fun a' ha' => hw a' (.tail _ ha')) u hu

/-- A function decoded from a tree that can be written is well formed. The
first pass names each value once, and its scope gives each value the type
that `Func.typeOf` gives it; the second pass gives the rest. -/
theorem decodeFunc_wellFormed {name : String} {params : List SDef}
    {results : List (Attr × TextPos)} {sbs : List SBlock} {f : Func d}
    (h : decodeFunc name params results sbs = .ok f) (hp : ∀ x ∈ params, x.Writable)
    (hr : ∀ r ∈ results, r.1.IsType) (hb : SBlock.WritableList sbs) : f.WellFormed := by
  unfold decodeFunc at h
  bind_step h with ⟨rs, e₁, h⟩
  bind_step h with ⟨sc₁, e₂, h⟩
  bind_step h with ⟨sc, e₃, h⟩
  bind_step h with ⟨ps, e₄, h⟩
  bind_step h with ⟨bs, e₅, h⟩
  cases h
  obtain ⟨k₁, n₁⟩ := define_holds e₂ e₄ Scope.holds_empty (by simp)
  obtain ⟨k₂, n₂⟩ := SBlock.adds sbs e₃ e₅ k₁ n₁
  simp only [List.nil_append] at k₂ n₂
  have hperm := Func.scopeDefs_perm (d := d) ⟨name, ps, rs, ⟨bs⟩⟩
  have hnd := (hperm.map (·.1)).nodup_iff.mp n₂
  have hsc : ∀ x, sc[x]? = Func.typeOf ⟨name, ps, rs, ⟨bs⟩⟩ x := fun x => Option.ext fun t => by
    rw [k₂ x t, Func.typeOf, find?_fst_eq_some hnd]
    simpa [Func.blocks] using hperm.mem_iff (a := (x, t))
  have hbs := SBlock.decodesTo sc name sbs hb bs e₅
  have hps := mapM_decodeDef_writable e₄ hp
  have hdefs : ∀ y ∈ Func.defs (d := d) ⟨name, ps, rs, ⟨bs⟩⟩, WritableDef y := by
    intro y hy
    simp only [Func.defs, Func.allBlocks, Func.blocks, List.mem_append, List.mem_flatMap,
      Block.defs] at hy
    rcases hy with hy | ⟨b, hb, hy | ⟨o, ho, hy⟩⟩
    · exact hps y hy
    · exact (hbs b hb).params y hy
    · exact ((hbs b hb).ops o ho).defs y hy
  refine ⟨hnd, fun y hy => (hdefs y hy).1, fun b hb => (hbs b hb).label, fun t ht => ?_,
    fun o ho => ?_⟩
  · simp only [Func.types, List.mem_append, List.mem_map] at ht
    rcases ht with ht | ⟨y, hy, rfl⟩
    · exact mapM_decodeType_writable (fun _ _ => rfl) e₁ hr t ht
    · exact (hdefs y hy).2
  · simp only [Func.allOps, List.mem_flatMap] at ho
    obtain ⟨b, hb, ho⟩ := ho
    have k := (hbs b hb).ops o ho
    refine ⟨k.name, k.attrs, ?_, k.results, fun s hs => k.succs s hs, k.loc⟩
    rw [← k.operands]
    exact List.map_congr_left fun x _ => (hsc x).symm

/-- An item decoded from a tree that can be written is a well-formed
function. -/
theorem decodeItem_wellFormed {si : SItem} {f : Func d} (h : decodeItem si = .ok (.func f))
    (hw : si.Writable) : f.WellFormed := by
  obtain ⟨kind, kindPos, name, params, results, attrs, body⟩ := si
  obtain ⟨hp, hr, hb⟩ := hw
  by_cases hk : kind = "func"
  · simp only [decodeItem, ne_eq, hk, not_true_eq_false, ↓reduceIte] at h
    split at h
    · cases h
    · cases h
    · bind_step h with ⟨f', e, h⟩
      cases h
      exact decodeFunc_wellFormed e hp hr trivial
    · bind_step h with ⟨f', e, h⟩
      cases h
      exact decodeFunc_wellFormed e hp hr hb
  · simp [decodeItem, hk, errorAt] at h

/-- Items decoded from trees that can be written are well-formed
functions. -/
theorem mapM_decodeItem_wellFormed : ∀ {sis : List SItem} {items : List (Item d)},
    sis.mapM decodeItem = .ok items → (∀ si ∈ sis, si.Writable) →
      ∀ f, Item.func f ∈ items → f.WellFormed
  | [], items, h, _ => by cases h; simp
  | si :: sis, items, h, hw => by
    rw [List.mapM_cons] at h
    bind_step h with ⟨⟨f'⟩, h₁, h⟩
    bind_step h with ⟨items', h₂, h⟩
    cases h
    intro f hf
    rcases List.mem_cons.mp hf with hf | hf
    · cases hf
      exact decodeItem_wellFormed h₁ (hw si (.head _))
    · exact mapM_decodeItem_wellFormed h₂ (fun si' hs' => hw si' (.tail _ hs')) f hf

/-- The decoding step: a module decoded from a tree that can be written is
well formed. -/
theorem decodeModule_wellFormed {s : SModule} {m : Module d} (h : decodeModule s = .ok m)
    (hw : s.Writable) : m.WellFormed := by
  unfold decodeModule at h
  bind_step h with ⟨items, e, h⟩
  cases h
  refine ⟨fun f hf => ?_, hw.2⟩
  simp only [Module.funcs, List.mem_map] at hf
  obtain ⟨⟨f'⟩, hi, rfl⟩ := hf
  exact mapM_decodeItem_wellFormed e hw.1 f' hi

end Fir
