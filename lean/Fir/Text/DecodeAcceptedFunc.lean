import Fir.Text.DecodeAccepted
import Fir.Text.SigAttrs

/-!
# A function and an external declaration as decoded

Decoding a function joins the two passes. The first pass names each value
once, and its scope gives each value the type that the function gives it,
since the scope's definitions are the function's definitions in another
order. So the scope can be replaced by the function's own types in what the
second pass accepts, and each decoded function is well formed. Its result
types decode as types do, from attributes written as types, and the
attributes after each result are that result's, held in the short form with
its parameters'.

An external declaration decodes its header as a function with no blocks
(ADR-2026-11-09-1547), so the function whose header it writes is well
formed too.
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

omit [DialectSignature d] [DialectValidation d] [LawfulDialectText d] in
/-- A function decoded with no blocks has a body of the core's kind with no
blocks. -/
theorem decodeFunc_nil_body {name : String} {params : List SDef}
    {results : List (Attr × TextPos)} {f : Func d} (h : decodeFunc name params results [] = .ok f) :
    f.body = ⟨none, []⟩ := by
  unfold decodeFunc at h
  bind_step h with ⟨rs, -, h⟩
  bind_step h with ⟨sc₁, -, h⟩
  bind_step h with ⟨sc, -, h⟩
  bind_step h with ⟨ps, -, h⟩
  bind_step h with ⟨bs, e₅, h⟩
  cases h
  simp only [decodeBlocks] at e₅
  cases e₅
  rfl

/-- An external declaration decoded from a tree that can be written is well
formed: the function whose header it writes is. -/
theorem decodeExternItem_wellFormed {kindPos : TextPos} {name : String} {params : List SDef}
    {paramAttrs : List (List (Attr × TextPos))} {variadic : Option TextPos}
    {results : List (Attr × TextPos)} {resultAttrs : List (List (Attr × TextPos))}
    {attrs : List (Attr × TextPos)} {body : SBody} {i : Item d}
    (h : decodeExternItem kindPos name params paramAttrs variadic results resultAttrs attrs body =
      .ok i)
    (hp : ∀ x ∈ params, x.Writable) (hr : ∀ r ∈ results, r.1.IsType)
    (hpw : ∀ as ∈ paramAttrs, ∀ a ∈ as, a.1.Writable) (hpl : paramAttrs.length = params.length)
    (hrw : ∀ as ∈ resultAttrs, ∀ a ∈ as, a.1.Writable)
    (hrl : resultAttrs.length = results.length - 1) (ha : ∀ a ∈ attrs, a.1.Writable) :
    i.WellFormed := by
  unfold decodeExternItem at h
  split at h
  · bind_step h with ⟨ras, e₁, h⟩
    bind_step h with ⟨f', e₃, h⟩
    cases h
    have hf' := decodeFunc_wellFormed e₃ hp hr trivial
    have hbody := decodeFunc_nil_body e₃
    obtain ⟨lp, lr⟩ := decodeFunc_lengths e₃
    obtain ⟨tr, wr⟩ := funcResultAttrs_wellFormed (externResultAttrs_eq_ok.mp e₁) hrl hrw ha
    have tp := trimAttrs_trimmed (paramAttrs.map fun as => as.map (·.1))
    have hw := hf'.withAttrs (v := variadic.isSome) (by simpa [lp, hpl] using tp) (lr ▸ tr)
      fun as has => by
        rcases List.mem_append.mp has with has | has
        · obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp (mem_of_mem_trimAttrs has)
          refine Attr.allWritable_of_mem fun a ha' => ?_
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha'
          exact hpw xs hxs y hy
        · exact wr as has
    rw [hbody] at hw
    exact hw
  · cases h

end Fir
