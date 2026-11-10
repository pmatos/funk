import Fir.Text.DecodeAccepted

/-!
# Functions, items and the module as decoded

Decoding a function joins the two passes. The first pass names each value
once, and its scope gives each value the type that the function gives it,
since the scope's definitions are the function's definitions in another
order. So the scope can be replaced by the function's own types in what the
second pass accepts, and each decoded function is well formed. Its result
types decode as types do, from attributes written as types.

An item decodes only as a `func` with no attributes, whose body holds
blocks or holds nothing, or as a `module` with no parameters, results or
attributes, whose body holds a dialect set and items, decoded in turn, or
holds nothing. Decoding a module keeps the location table as it was read. So a module decoded from a tree that can be written is well
formed: the decoding step.
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

/-- A `func` decoded from a tree that can be written is well formed. -/
theorem decodeFuncItem_wellFormed {kindPos : TextPos} {name : String} {params : List SDef}
    {results attrs : List (Attr × TextPos)} {body : SBody} {i : Item d}
    (h : decodeFuncItem kindPos name params results attrs body = .ok i)
    (hp : ∀ x ∈ params, x.Writable) (hr : ∀ r ∈ results, r.1.IsType) (hb : body.Writable) :
    i.WellFormed := by
  unfold decodeFuncItem at h
  split at h
  · cases h
  · cases h
  · cases h
  · bind_step h with ⟨f', e, h⟩
    cases h
    exact decodeFunc_wellFormed e hp hr trivial
  · bind_step h with ⟨f', e, h⟩
    cases h
    exact decodeFunc_wellFormed e hp hr hb

-- The two theorems recurse together, so both take the dialect's lawful
-- text, which only the first states it needs.
set_option linter.unusedSectionVars false in
mutual
/-- An item decoded from a tree that can be written is well formed, at any
depth. -/
theorem decodeItem_wellFormed : ∀ {si : SItem} {i : Item d}, decodeItem si = .ok i →
    si.Writable → i.WellFormed
  | ⟨kind, kindPos, name, params, results, attrs, .items ds sis⟩, i, h, hw => by
    obtain ⟨hp, hr, hd, hs⟩ := hw
    rw [decodeItem.eq_def] at h
    dsimp only at h
    by_cases hk : kind = "func"
    · simp only [hk, ↓reduceIte] at h
      exact decodeFuncItem_wellFormed h hp hr ⟨hd, hs⟩
    · by_cases hm : kind = "module"
      · simp only [hm, ↓reduceIte] at h
        bind_step h with ⟨_, -, h⟩
        bind_step h with ⟨is, e, h⟩
        cases h
        exact ⟨hd, decodeItems_wellFormed e hs⟩
      · simp [hk, hm, errorAt] at h
  | ⟨kind, kindPos, name, params, results, attrs, .blocks bs⟩, i, h, hw => by
    obtain ⟨hp, hr, hb⟩ := hw
    rw [decodeItem.eq_def] at h
    dsimp only at h
    by_cases hk : kind = "func"
    · simp only [hk, ↓reduceIte] at h
      exact decodeFuncItem_wellFormed h hp hr hb
    · by_cases hm : kind = "module"
      · simp only [hm, ↓reduceIte] at h
        bind_step h with ⟨_, -, h⟩
        cases bs with
        | nil =>
          cases h
          exact ⟨by simp, trivial⟩
        | cons => simp [errorAt] at h
      · simp [hk, hm, errorAt] at h

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

/-- The decoding step: a module decoded from a tree that can be written is
well formed. -/
theorem decodeModule_wellFormed {s : SModule} {m : Module d} (h : decodeModule s = .ok m)
    (hw : s.Writable) : m.WellFormed := by
  unfold decodeModule at h
  bind_step h with ⟨items, e, h⟩
  cases h
  rw [← decodeItems_eq_mapM] at e
  exact ⟨hw.1, (Item.wellFormedList_iff _).mp
    (decodeItems_wellFormed e ((SItem.writableList_iff _).mpr hw.2.1)), hw.2.2⟩

end Fir
