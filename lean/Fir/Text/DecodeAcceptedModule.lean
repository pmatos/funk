import Fir.Text.DecodeAcceptedFunc
import Fir.Text.GlobalLaws

/-!
# Items and the module as decoded

An item decodes only as a `func`, whose body holds blocks or holds nothing,
as an external declaration, as a `module` with no parameters, results or
attributes, whose body holds a dialect set and items, decoded in turn, or
holds nothing, as an aggregate's layout whose numbers are within the limit
and whose fields' types are written as types and decode back, as a global
whose numbers are within the limit, or as an item of a dialect's kind, whose kind is a word of a dialect and whose body is
empty, with its attributes as read. Decoding a
module decodes each entry of its data layout, which is within the limit
when it decodes, and keeps the location table as it was read. So a module decoded from a
tree that can be written is well formed: the decoding step.
-/

namespace Fir

open Text

variable {d : Dialect} [DialectSignature d] [DialectValidation d] [DialectText d]
  [LawfulDialectText d]

/-- An item of a dialect's kind decoded from a tree that can be written is
well formed. -/
theorem decodeDialectItem_wellFormed {kind : String} {kindPos : TextPos} {name : String}
    {params : List SDef} {results attrs : List (Attr × TextPos)} {body : SBody} {i : Item d}
    (h : decodeDialectItem kind kindPos name params results attrs body = .ok i)
    (hk : isDialectWord kind) (hp : ∀ x ∈ params, x.Writable) (hr : ∀ r ∈ results, r.1.IsType)
    (ha : ∀ a ∈ attrs, a.1.Writable) : i.WellFormed := by
  unfold decodeDialectItem at h
  split at h
  · bind_step h with ⟨rs, e₁, h⟩
    bind_step h with ⟨ps, e₂, h⟩
    cases h
    have hps := mapM_decodeDef_writable e₂ hp
    refine ⟨hk, fun x hx => (hps x hx).1, fun t ht => ?_,
      Attr.allWritable_of_mem fun a h' => ?_⟩
    · simp only [DialectItem.types, List.mem_append, List.mem_map] at ht
      rcases ht with ⟨y, hy, rfl⟩ | ht
      · exact (hps y hy).2
      · exact mapM_decodeType_writable (fun _ _ => rfl) e₁ hr t ht
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h'
      exact ha b hb
  · cases h

/-- Fields decoded from attributes that can be written have their numbers
within the limit, and their types are written as types and decode back. -/
theorem decodeFields_wellFormed : ∀ {ss : List (Attr × TextPos)} {fs : List (Field d)},
    ss.mapM decodeField = .ok fs → (∀ a ∈ ss, a.1.Writable) → ∀ f ∈ fs,
      f.offset ≤ Aggregate.limit ∧ (∀ c ∈ f.count, c ≤ Aggregate.limit) ∧
        (tyAttr f.ty).IsType ∧ decodeTy (tyAttr f.ty) = some f.ty
  | [], fs, h, _ => by cases h; simp
  | (a, p) :: ss, fs, h, hw => by
    rw [List.mapM_cons] at h
    bind_step h with ⟨f, h₁, h⟩
    bind_step h with ⟨fs', h₂, h⟩
    cases h
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp only [decodeField] at h₁
      cases hd : Field.decode (d := d) a with
      | none => rw [hd] at h₁; cases h₁
      | some f' =>
        rw [hd] at h₁
        cases h₁
        exact Field.wellFormed_of_decode hd (hw _ (.head _)) LawfulDialectText.encode_decodeTy
    · exact decodeFields_wellFormed h₂ (fun a' ha' => hw a' (.tail _ ha')) g hg

/-- An aggregate's layout decoded from attributes that can be written is
well formed. -/
theorem decodeAggregate_wellFormed {kindPos : TextPos} {name : String} {params : List SDef}
    {results attrs : List (Attr × TextPos)} {body : SBody} {i : Item d}
    (h : decodeAggregate kindPos name params results attrs body = .ok i)
    (ha : ∀ a ∈ attrs, a.1.Writable) : i.WellFormed := by
  unfold decodeAggregate at h
  split at h
  · cases h
  · cases h
  · split at h
    · rename_i hm hs hal
      bind_step h with ⟨fs, e, h⟩
      cases h
      have hF := decodeFields_wellFormed e fun x hx => ha x (by simp [hx])
      exact ⟨⟨Aggregate.le_of_decodeNumber hm, Aggregate.le_of_decodeNumber hs,
        Aggregate.le_of_decodeNumber hal, fun f hf => ⟨(hF f hf).1, (hF f hf).2.1⟩⟩,
        fun t ht => by
          obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ht
          exact (hF f hf).2.2⟩
    all_goals cases h
  · cases h
  · cases h

omit [DialectValidation d] [LawfulDialectText d] in
/-- A global decoded from its attributes has its numbers within the limit. -/
theorem decodeGlobal_wellFormed {kindPos : TextPos} {name : String} {params : List SDef}
    {results attrs : List (Attr × TextPos)} {body : SBody} {i : Item d}
    (h : decodeGlobal kindPos name params results attrs body = .ok i) : i.WellFormed := by
  unfold decodeGlobal at h
  split at h
  · cases h
  · cases h
  · split at h
    · rename_i g hg
      cases h
      exact Global.inLimits_of_decodeAttrs hg
    · cases h
  · cases h

-- The two theorems recurse together, so both take the dialect's lawful
-- text, which only the first states it needs.
set_option linter.unusedSectionVars false in
mutual
/-- An item decoded from a tree that can be written is well formed, at any
depth. -/
theorem decodeItem_wellFormed : ∀ {si : SItem} {i : Item d}, decodeItem si = .ok i →
    si.Writable → i.WellFormed
  | ⟨kind, kindPos, name, params, paramAttrs, variadic, results, resultAttrs, attrs,
      .items ds sis⟩, i, h, hw => by
    obtain ⟨hp, hr, ha, ⟨hd, hs⟩, hpw, hrw, hpl, hrl⟩ := hw
    rw [decodeItem.eq_def] at h
    dsimp only at h
    by_cases hk : kind = "func"
    · simp only [hk, ↓reduceIte] at h
      exact decodeFuncItem_wellFormed h hp hr ⟨hd, hs⟩ hpw hpl hrw hrl ha
    · simp only [hk, ↓reduceIte] at h
      by_cases hx : kind = "extern"
      · simp only [hx, ↓reduceIte] at h
        exact decodeExternItem_wellFormed h hp hr hpw hpl hrw hrl ha
      simp only [hx, ↓reduceIte] at h
      bind_step h with ⟨_, -, h⟩
      by_cases hm : kind = "module"
      · simp only [hm, ↓reduceIte] at h
        bind_step h with ⟨_, -, h⟩
        bind_step h with ⟨is, e, h⟩
        cases h
        exact ⟨hd, decodeItems_wellFormed e hs⟩
      · simp only [hm, ↓reduceIte] at h
        by_cases hg : kind = "aggregate"
        · simp only [hg, ↓reduceIte] at h
          exact decodeAggregate_wellFormed h ha
        simp only [hg, ↓reduceIte] at h
        by_cases hgl : kind = "global"
        · simp only [hgl, ↓reduceIte] at h
          exact decodeGlobal_wellFormed h
        simp only [hgl, ↓reduceIte] at h
        split at h
        · exact decodeDialectItem_wellFormed h (by assumption) hp hr ha
        · cases h
  | ⟨kind, kindPos, name, params, paramAttrs, variadic, results, resultAttrs, attrs,
      .blocks bs⟩, i, h, hw => by
    obtain ⟨hp, hr, ha, hb, hpw, hrw, hpl, hrl⟩ := hw
    rw [decodeItem.eq_def] at h
    dsimp only at h
    by_cases hk : kind = "func"
    · simp only [hk, ↓reduceIte] at h
      exact decodeFuncItem_wellFormed h hp hr hb hpw hpl hrw hrl ha
    · simp only [hk, ↓reduceIte] at h
      by_cases hx : kind = "extern"
      · simp only [hx, ↓reduceIte] at h
        exact decodeExternItem_wellFormed h hp hr hpw hpl hrw hrl ha
      simp only [hx, ↓reduceIte] at h
      bind_step h with ⟨_, -, h⟩
      by_cases hm : kind = "module"
      · simp only [hm, ↓reduceIte] at h
        bind_step h with ⟨_, -, h⟩
        cases bs with
        | nil =>
          cases h
          exact ⟨by simp, trivial⟩
        | cons => simp [errorAt] at h
      · simp only [hm, ↓reduceIte] at h
        by_cases hg : kind = "aggregate"
        · simp only [hg, ↓reduceIte] at h
          exact decodeAggregate_wellFormed h ha
        simp only [hg, ↓reduceIte] at h
        by_cases hgl : kind = "global"
        · simp only [hgl, ↓reduceIte] at h
          exact decodeGlobal_wellFormed h
        simp only [hgl, ↓reduceIte] at h
        split at h
        · exact decodeDialectItem_wellFormed h (by assumption) hp hr ha
        · cases h

/-- Items decoded from trees that can be written are well formed. -/
theorem decodeItems_wellFormed : ∀ {sis : List SItem} {is : List (Item d)},
    decodeItems sis = .ok is → SItem.WritableList sis → Item.WellFormedList is
  | [], is, h, _ => by cases h; trivial
  | si :: sis, is, h, hw => by
    rw [decodeItems.eq_def] at h
    dsimp only at h
    bind_step h with ⟨i, h₁, h⟩
    bind_step h with ⟨is', h₂, h⟩
    cases h
    exact ⟨decodeItem_wellFormed h₁ hw.1, decodeItems_wellFormed h₂ hw.2⟩
end

omit [DialectSignature d] [DialectValidation d] [DialectText d] [LawfulDialectText d] in
/-- Entries of a data layout that decode have their numbers within the
limit. -/
theorem decodeLayout_inLimits : ∀ {ss : List (Attr × TextPos)} {es : List MemLayout},
    ss.mapM decodeMemLayout = .ok es → ∀ e ∈ es, e.InLimits
  | [], es, h, e, he => by cases h; simp at he
  | (a, p) :: ss, es, h, e, he => by
    rw [List.mapM_cons] at h
    bind_step h with ⟨x, h₁, h⟩
    bind_step h with ⟨xs, h₂, h⟩
    cases h
    rcases List.mem_cons.mp he with rfl | he
    · dsimp only [decodeMemLayout] at h₁
      cases hd : MemLayout.decode a with
      | some y =>
        rw [hd] at h₁
        simp only [pure, Except.pure, Except.ok.injEq] at h₁
        subst h₁
        exact MemLayout.inLimits_of_decode hd
      | none => rw [hd] at h₁; simp [errorAt] at h₁
    · exact decodeLayout_inLimits h₂ e he

/-- The decoding step: a module decoded from a tree that can be written is
well formed. -/
theorem decodeModule_wellFormed {s : SModule} {m : Module d} (h : decodeModule s = .ok m)
    (hw : s.Writable) : m.WellFormed := by
  unfold decodeModule at h
  bind_step h with ⟨layout, eL, h⟩
  bind_step h with ⟨items, e, h⟩
  cases h
  rw [← decodeItems_eq_mapM] at e
  exact ⟨hw.1, decodeLayout_inLimits eL, (Item.wellFormedList_iff _).mp
    (decodeItems_wellFormed e ((SItem.writableList_iff _).mpr hw.2.1)), hw.2.2⟩

end Fir
