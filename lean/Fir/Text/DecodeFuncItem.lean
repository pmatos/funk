import Fir.Text.DecodeBlocks
import Fir.Text.SigAttrs

/-!
# Decoding a function's item and an external declaration

A function's item is a `func` whose attributes after each result are that
result's, and whose body is its blocks. Decoding it decodes the attributes
of its results, then its result types, builds the scope with the first
pass, decodes the parameters, and decodes the blocks in the scope with the
second pass. On a tree that erases to a well-formed function's tree, at any
positions, it gives the function back.

An external declaration is an `extern` whose header is a function's with no
blocks (ADR-2026-11-09-1547), and its body is empty. It decodes as that
function's header does, so on a tree that erases to its tree it gives the
declaration back when the function whose header it writes is well formed.
-/

namespace Fir

open Text

variable {d : Dialect} [DialectText d]

/-- Binding a result that a step gives runs what follows on it. -/
theorem bind_eq_of {ε α β : Type} {x : Except ε α} {a : α} {k : α → Except ε β}
    (h : x = .ok a) : (x >>= k) = k a := by
  subst h
  rfl

/-- The result types of a function's tree decode as the function's result
types, when each decodes back to itself. -/
theorem mapM_decodeType {g : Attr × TextPos → Except ParseError d.Ty}
    (hg : ∀ a p, g (a, p) = decodeType a p) :
    ∀ {as : List (Attr × TextPos)} {ts : List d.Ty}, as.map (·.1) = ts.map tyAttr →
      (∀ t ∈ ts, decodeTy (tyAttr t) = some t) → as.mapM g = .ok ts
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | (a, p) :: as, t :: ts, h, ht => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have hx : g (tyAttr t, p) = .ok t := by
      rw [hg]
      simp only [decodeType, ht t (.head _)]
    simp only [List.mapM_cons, hx, ok_bind,
      mapM_decodeType hg h fun t' ht' => ht t' (.tail _ ht')] <;> rfl

variable [DialectSignature d] [DialectValidation d] [LawfulDialectText d]

/-- A function's symbol, parameters, results and body decode back from its
tree, at any positions, when it is well formed. -/
theorem Func.WellFormed.decodeFunc_eq {f : Func d} (hf : f.WellFormed) {sps : List SDef}
    {srs : List (Attr × TextPos)} {sbs : List SBlock}
    (hp : sps.map SDef.erase = f.params.map defTree) (hr : srs.map (·.1) = f.results.map tyAttr)
    (hb : SBlock.eraseList sbs = Block.treeList f.body.blocks) :
    Text.decodeFunc f.name sps srs sbs = .ok ⟨f.name, f.params, f.results, f.body, [], [], false⟩ := by
  obtain ⟨sc₁, sc, e₁, e₂, hsc⟩ := hf.scope hp hb
  have hps : sps.mapM decodeDef = .ok f.params :=
    mapM_decodeDef hp fun y hy => hf.decodeTy_def (List.mem_append_left _ hy)
  have hbs := Block.decodesList sc f.name f.body.blocks (hf.decodesIn hsc) sbs hb
  unfold Text.decodeFunc
  refine (bind_eq_of (a := f.results) ?_).trans ?_
  · exact mapM_decodeType (fun _ _ => rfl) hr fun t ht =>
      (hf.types t (List.mem_append_left _ ht)).2
  · have hk := hf.bodyKind
    simp only [e₁, ok_bind, e₂, hps, hbs]
    obtain ⟨_, _, _, ⟨_, _⟩, _, _, _⟩ := f
    simp only at hk
    subst hk
    rfl

omit [DialectValidation d] [LawfulDialectText d] in
/-- The attributes of a function's results decode back from its tree, at
any positions, when it is well formed. -/
theorem Func.WellFormed.funcResultAttrs_eq {f : Func d} (hf : f.WellFormed)
    {results : List (Attr × TextPos)} {resultAttrs : List (List (Attr × TextPos))}
    {attrs : List (Attr × TextPos)} (hr : results.map (·.1) = f.results.map tyAttr)
    (hra : resultAttrs.map (·.map (·.1)) = f.resultAttrsAll.dropLast)
    (ha : attrs.map (·.1) = f.resultAttrsAll.getLast?.getD []) :
    funcResultAttrs results resultAttrs attrs = .ok f.resultAttrs := by
  rcases hfr : f.results with _ | ⟨t, ts⟩
  · have h0 : f.resultAttrs = [] := by
      have := hf.resultAttrs.1
      rw [hfr] at this
      exact List.eq_nil_of_length_eq_zero (Nat.le_zero.mp this)
    simp only [Func.resultAttrsAll, hfr, List.length_nil, padAttrs, List.range_zero,
      List.map_nil, List.dropLast_nil, List.getLast?_nil, Option.getD_none] at hra ha
    rw [hfr, List.map_nil, List.map_eq_nil_iff] at hr
    obtain rfl := hr
    obtain rfl := List.map_eq_nil_iff.mp hra
    obtain rfl := List.map_eq_nil_iff.mp ha
    rw [h0]
    rfl
  · obtain ⟨r, rs, rfl⟩ : ∃ r rs, results = r :: rs := by
      rcases results with _ | ⟨r, rs⟩
      · rw [hfr] at hr; simp at hr
      · exact ⟨r, rs, rfl⟩
    have hne : f.resultAttrsAll ≠ [] := by
      rw [← List.length_pos_iff, Func.resultAttrsAll, length_padAttrs, hfr]; simp
    have hall : (resultAttrs ++ [attrs]).map (·.map (·.1)) = f.resultAttrsAll := by
      rw [List.map_append, hra, List.map_singleton, ha, dropLast_append_getLast hne]
    unfold funcResultAttrs
    rw [hall, Func.resultAttrsAll, trimAttrs_padAttrs hf.resultAttrs]
    rfl

/-- A function's item decodes back from a tree that erases to its tree, when
the function is well formed. -/
theorem Func.WellFormed.decodeItem_eq {f : Func d} (hf : f.WellFormed) {si : SItem}
    (h : si.erase = f.tree) : Text.decodeItem si = .ok (.func f) := by
  obtain ⟨hk, hn, hp, hpa, hv, hr, hra, ha, bs, hb, hbs⟩ := SItem.erase_eq_funcTree h
  obtain ⟨kind, kindPos, name, params, paramAttrs, variadic, results, resultAttrs, attrs, body⟩ :=
    si
  dsimp only at hk hn hp hpa hv hr hra ha hb
  subst hk hn hb
  rw [Text.decodeItem.eq_def]
  simp only [↓reduceIte, decodeFuncItem, hf.funcResultAttrs_eq hr hra ha, funcBlocks,
    ok_bind, pure_bind, hf.decodeFunc_eq hp hr hbs]
  rw [hpa, Func.paramAttrsAll, trimAttrs_padAttrs hf.paramAttrs, hv]
  rfl

/-- An external declaration decodes back from a tree that erases to its
tree, at any positions, when the function whose header it writes is well
formed. -/
theorem Extern.decodeItem_eq {e : Extern d} (he : e.func.WellFormed) {si : SItem}
    (h : si.erase = e.tree) : Text.decodeItem si = .ok (.extern e) := by
  obtain ⟨kind, kindPos, name, params, paramAttrs, variadic, results, resultAttrs, attrs, body⟩ :=
    si
  have hk : kind = "extern" := by
    simp only [SItem.erase, Extern.tree, Func.tree, SItem.mk.injEq] at h
    exact h.1
  have h' : (SItem.mk "func" kindPos name params paramAttrs variadic results resultAttrs attrs
      body).erase = e.func.tree := by
    simp only [SItem.erase, Extern.tree, Func.tree, SItem.mk.injEq, true_and] at h ⊢
    exact h.2
  obtain ⟨-, hn, hp, hpa, hv, hr, hra, ha, bs, hb, hbs⟩ := SItem.erase_eq_funcTree h'
  dsimp only at hn hp hpa hv hr hra ha hb
  subst hk hn hb
  obtain rfl : bs = [] := SBlock.eraseList_eq_nil hbs
  rw [Text.decodeItem.eq_def]
  simp only [String.reduceEq, ↓reduceIte, decodeExternItem,
    externResultAttrs_eq_ok.mpr (he.funcResultAttrs_eq hr hra ha), ok_bind, he.decodeFunc_eq hp hr hbs]
  rw [hpa, Func.paramAttrsAll, trimAttrs_padAttrs he.paramAttrs, hv]
  rfl

end Fir
