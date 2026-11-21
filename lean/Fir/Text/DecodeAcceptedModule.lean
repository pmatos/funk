import Fir.Text.DecodeAccepted
import Fir.Text.GlobalLaws
import Fir.Text.SigAttrs

/-!
# Functions, items and the module as decoded

Decoding a function joins the two passes. The first pass names each value
once, and its scope gives each value the type that the function gives it,
since the scope's definitions are the function's definitions in another
order. So the scope can be replaced by the function's own types in what the
second pass accepts, and each decoded function is well formed. Its result
types decode as types do, from attributes written as types.

An item decodes only as a `func` with no attributes, whose body holds
blocks or holds nothing, as a `module` with no parameters, results or
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
  have hperm := Func.scopeDefs_perm (d := d) ⟨name, ps, rs, ⟨none, bs⟩, [], [], false⟩
  have hnd := (hperm.map (·.1)).nodup_iff.mp n₂
  have hsc : ∀ x, sc[x]? = Func.typeOf ⟨name, ps, rs, ⟨none, bs⟩, [], [], false⟩ x :=
    fun x => Option.ext fun t => by
    rw [k₂ x t, Func.typeOf, find?_fst_eq_some hnd]
    simpa [Func.blocks] using hperm.mem_iff (a := (x, t))
  have hbs := SBlock.decodesTo sc name sbs hb bs e₅
  have hps := mapM_decodeDef_writable e₄ hp
  have hdefs : ∀ y ∈ Func.defs (d := d) ⟨name, ps, rs, ⟨none, bs⟩, [], [], false⟩,
      WritableDef y := by
    intro y hy
    simp only [Func.defs, Func.allBlocks, Func.blocks, List.mem_append, List.mem_flatMap,
      Block.defs] at hy
    rcases hy with hy | ⟨b, hb, hy | ⟨o, ho, hy⟩⟩
    · exact hps y hy
    · exact (hbs b hb).params y hy
    · exact ((hbs b hb).ops o ho).defs y hy
  refine ⟨hnd, fun y hy => (hdefs y hy).1, fun b hb => (hbs b hb).label, fun t ht => ?_,
    fun o ho => ?_, rfl, fun o ho => ?_, ⟨Nat.zero_le _, by simp⟩, ⟨Nat.zero_le _, by simp⟩,
    by simp⟩
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
  · simp only [Func.allOps, List.mem_flatMap] at ho
    obtain ⟨b, hb, ho⟩ := ho
    exact ((hbs b hb).ops o ho).kinds

omit [DialectSignature d] [DialectValidation d] [LawfulDialectText d] in
/-- Decoding a function gives one parameter for each definition and one
result for each type. -/
theorem decodeFunc_lengths {name : String} {params : List SDef}
    {results : List (Attr × TextPos)} {sbs : List SBlock} {f : Func d}
    (h : decodeFunc name params results sbs = .ok f) :
    f.params.length = params.length ∧ f.results.length = results.length := by
  have hl : ∀ {α β : Type} {g : α → Except ParseError β} {xs : List α} {ys : List β},
      xs.mapM g = .ok ys → ys.length = xs.length := by
    intro α β g xs
    induction xs with
    | nil => intro ys h; cases h; rfl
    | cons x xs ih =>
      intro ys h
      rw [List.mapM_cons] at h
      bind_step h with ⟨y, -, h⟩
      bind_step h with ⟨ys', h₂, h⟩
      cases h
      simp [ih h₂]
  unfold decodeFunc at h
  bind_step h with ⟨rs, e₁, h⟩
  bind_step h with ⟨sc₁, -, h⟩
  bind_step h with ⟨sc, -, h⟩
  bind_step h with ⟨ps, e₄, h⟩
  bind_step h with ⟨bs, -, h⟩
  cases h
  exact ⟨hl e₄, hl e₁⟩

omit [DialectValidation d] [LawfulDialectText d] in
/-- A function that is well formed stays so with attributes for its
parameters and results that have the form a function holds and can be
written, and with its parameters ending in `...` or not. -/
theorem Func.WellFormed.withAttrs {f : Func d} (hf : f.WellFormed) {pa ra : List (List Attr)}
    {v : Bool} (hpa : AttrsTrimmed f.params.length pa) (hra : AttrsTrimmed f.results.length ra)
    (hw : ∀ as ∈ pa ++ ra, Attr.AllWritable as) :
    (⟨f.name, f.params, f.results, f.body, pa, ra, v⟩ : Func d).WellFormed :=
  ⟨hf.namesUnique, hf.names, hf.labels, hf.types, hf.ops, hf.bodyKind, hf.kinds, hpa, hra, hw⟩

/-- Attributes that can each be written can all be written. -/
theorem Attr.allWritable_of_mem : ∀ {as : List Attr}, (∀ a ∈ as, a.Writable) → Attr.AllWritable as
  | [], _ => trivial
  | _ :: _, h => ⟨h _ (.head _), Attr.allWritable_of_mem fun a ha => h a (.tail _ ha)⟩

/-- The attributes of a func's results as decoded have the form a function
holds, and can be written, from a tree that can be written. -/
theorem funcResultAttrs_wellFormed {results : List (Attr × TextPos)}
    {resultAttrs : List (List (Attr × TextPos))} {attrs : List (Attr × TextPos)}
    {ras : List (List Attr)} (h : funcResultAttrs results resultAttrs attrs = .ok ras)
    (hl : resultAttrs.length = results.length - 1) (hw : ∀ as ∈ resultAttrs, ∀ a ∈ as, a.1.Writable)
    (ha : ∀ a ∈ attrs, a.1.Writable) :
    AttrsTrimmed results.length ras ∧ ∀ as ∈ ras, Attr.AllWritable as := by
  unfold funcResultAttrs at h
  split at h
  · cases h
  · cases h
    rename_i hne
    have hw' : ∀ as ∈ trimAttrs ((resultAttrs ++ [attrs]).map (·.map (·.1))),
        Attr.AllWritable as := by
      intro as has
      obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp (mem_of_mem_trimAttrs has)
      refine Attr.allWritable_of_mem fun a ha' => ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha'
      rcases List.mem_append.mp hxs with hxs | hxs
      · exact hw xs hxs y hy
      · obtain rfl := List.mem_singleton.mp hxs
        exact ha y hy
    refine ⟨?_, hw'⟩
    rcases results with _ | ⟨r, rs⟩
    · obtain rfl : attrs = [] := by
        cases attrs with
        | nil => rfl
        | cons a _ => exact (hne a.1 a.2 _ rfl rfl).elim
      obtain rfl : resultAttrs = [] := List.eq_nil_of_length_eq_zero hl
      exact ⟨Nat.le_refl _, by simp [trimAttrs]⟩
    · have ht := trimAttrs_trimmed ((resultAttrs ++ [attrs]).map (·.map (·.1)))
      refine ⟨Nat.le_trans ht.1 ?_, ht.2⟩
      simp [hl]

/-- A `func` decoded from a tree that can be written is well formed. -/
theorem decodeFuncItem_wellFormed {kindPos : TextPos} {name : String} {params : List SDef}
    {paramAttrs : List (List (Attr × TextPos))} {variadic : Option TextPos}
    {results : List (Attr × TextPos)} {resultAttrs : List (List (Attr × TextPos))}
    {attrs : List (Attr × TextPos)} {body : SBody} {i : Item d}
    (h : decodeFuncItem kindPos name params paramAttrs variadic results resultAttrs attrs body =
      .ok i)
    (hp : ∀ x ∈ params, x.Writable) (hr : ∀ r ∈ results, r.1.IsType) (hb : body.Writable)
    (hpw : ∀ as ∈ paramAttrs, ∀ a ∈ as, a.1.Writable) (hpl : paramAttrs.length = params.length)
    (hrw : ∀ as ∈ resultAttrs, ∀ a ∈ as, a.1.Writable)
    (hrl : resultAttrs.length = results.length - 1) (ha : ∀ a ∈ attrs, a.1.Writable) :
    i.WellFormed := by
  unfold decodeFuncItem at h
  bind_step h with ⟨ras, e₁, h⟩
  bind_step h with ⟨bs, e₂, h⟩
  bind_step h with ⟨f', e₃, h⟩
  cases h
  have hbs : SBlock.WritableList bs := by
    unfold funcBlocks at e₂
    split at e₂
    · cases e₂
    · cases e₂
    · cases e₂; trivial
    · cases e₂; exact hb
  have hf' := decodeFunc_wellFormed e₃ hp hr hbs
  obtain ⟨lp, lr⟩ := decodeFunc_lengths e₃
  obtain ⟨tr, wr⟩ := funcResultAttrs_wellFormed e₁ hrl hrw ha
  have tp := trimAttrs_trimmed (paramAttrs.map fun as => as.map (·.1))
  refine hf'.withAttrs (by simpa [lp, hpl] using tp) (lr ▸ tr) fun as has => ?_
  rcases List.mem_append.mp has with has | has
  · obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp (mem_of_mem_trimAttrs has)
    refine Attr.allWritable_of_mem fun a ha' => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha'
    exact hpw xs hxs y hy
  · exact wr as has


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
