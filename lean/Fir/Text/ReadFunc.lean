import Fir.Text.ReadBlocks
import Fir.Text.ReadParams

/-!
# Reading a printed function

A function's tokens after its kind read back as its tree, whatever follows
them. The reader of an item chooses on the next token at three places: it
reads the parameters, each with its attributes, when anything but `)`
follows the `(`, and none when `)` does; the results after `->` when one follows the `)`; and
the body as items when a word follows the `{`, and as blocks otherwise. A
function's parameters, results and blocks decide which way the printed
tokens go, and the proof follows that way and rules out the other. A lemma
on one step followed by another lets it prove each part on its own: what
the part reads, then what the rest of the reader does with it.

The tokens after the `{` start with a block's label, or are the `}` when
the function has no block, and never with a word. So the reader of an item
reads every printed body as blocks, the empty one included, which is how
the tree of a function writes it. The attributes of each result are read
with it, so no attribute is left for the item, since a `{` follows the
results; the tree of a function writes the attributes of its last result
as the item's.

An item of a dialect's kind reads back the same way, with its attributes
read between its results and its `{`, as those of its last result when it
has results, and its empty body read as no blocks
(ADR-2026-11-09-1543). Its attributes start with a word, a number, a string
or a symbol, never with `->`, `,` or `(`, so they do not change the way the
reader goes.
-/

namespace Fir

open Text

variable {d : Dialect} [DialectText d]

/-- Reading `X`, then `K` on what it read: when `X` gives a result with `Q`,
and `K` gives a result with `P` from every result with `Q`, the two give a
result with `P`. -/
theorem bind_reads {ε α γ δ : Type} {X : Except ε α} {K : α → Except ε (γ × δ)}
    (Q : α → Prop) {P : γ → δ → Prop} (hX : ∃ v, X = .ok v ∧ Q v)
    (hK : ∀ v, Q v → ∃ a r, K v = .ok (a, r) ∧ P a r) :
    ∃ a r, (X >>= K) = .ok (a, r) ∧ P a r := by
  obtain ⟨v, hv, hq⟩ := hX
  rw [hv]
  exact hK v hq

/-- A function's parameters, with their attributes, as the reader of
parameters takes them. -/
theorem Func.paramsTokens_eq (f : Func d) :
    f.paramsTokens = paramsToks (f.params.zip f.paramAttrsAll) f.variadic := by
  have hl : (f.params.zip f.paramAttrsAll).isEmpty = f.params.isEmpty := by
    cases h : f.params <;> simp [Func.paramAttrsAll, h, padAttrs, List.range_succ_eq_map]
  simp only [Func.paramsTokens, paramsToks, ellipsisToks, hl]
  rfl

/-- `readItem` reads the tokens of a function after its kind as the
function's tree, of whatever kind the word before them names, when each
type it writes is written as a type. An external declaration writes the
header of a function with no blocks after its kind `extern`. -/
theorem Func.readsAs (k : String) (f : Func d) (ht : ∀ t ∈ f.types, (tyAttr t).IsType)
    (p : TextPos) :
    Reads (readItem k p) SItem.erase { f.tree with kind := k } f.tokens.tail (fun _ => True) := by
  have hres : ∀ t ∈ f.results, (tyAttr t).IsType := fun t h => ht t (List.mem_append_left _ h)
  have hpar : ∀ x ∈ f.params, (tyAttr x.2).IsType := fun x hx =>
    ht x.2 (List.mem_append_right _ (List.mem_map_of_mem (List.mem_append_left _ hx)))
  have hblk : ∀ b ∈ Block.allBlocks f.body.blocks, ∀ x ∈ b.defs, (tyAttr x.2).IsType :=
    fun b hb x hx => ht x.2 (List.mem_append_right _ (List.mem_map_of_mem
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨b, hb, hx⟩))))
  clear ht
  have hlp : f.params.length ≤ f.paramAttrsAll.length := by simp [Func.paramAttrsAll]
  have hlr : f.results.length ≤ f.resultAttrsAll.length := by simp [Func.resultAttrsAll]
  -- The parameters, each with its attributes, and the results.
  obtain ⟨PS, hPSd⟩ : ∃ PS, f.params.zip f.paramAttrsAll = PS := ⟨_, rfl⟩
  obtain ⟨RS, hRSd⟩ : ∃ RS, (f.results.zip f.resultAttrsAll).map (fun r => (tyAttr r.1, r.2)) = RS :=
    ⟨_, rfl⟩
  have hPS : ∀ q ∈ PS, (tyAttr q.1.2).IsType := fun q hq => hpar _ (List.of_mem_zip (hPSd ▸ hq)).1
  have hRS : ∀ r ∈ RS, r.1.IsType := fun r hr => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (hRSd ▸ hr)
    exact hres _ (List.of_mem_zip hq).1
  have hRt : f.resultsTokens = if f.results.isEmpty then [] else
      .arrow :: [Tok.comma].intercalate (RS.map resultToks) := by
    subst hRSd
    simp only [Func.resultsTokens, List.map_map]
    rfl
  have hPe : PS = [] ↔ f.params = [] := by
    subst hPSd; rcases hp : f.params with _ | ⟨x, xs⟩ <;> simp [Func.paramAttrsAll, padAttrs, hp]
  have hRe : RS = [] ↔ f.results = [] := by
    subst hRSd; rcases hr : f.results with _ | ⟨x, xs⟩ <;> simp [Func.resultAttrsAll, padAttrs, hr]
  rintro ts rest h -
  simp only [Func.tokens, List.tail_cons, List.cons_append, List.append_assoc,
    List.nil_append, f.paramsTokens_eq, hRt, hPSd] at h
  take_tok h
  take_tok h
  rw [readItem.eq_1]
  simp only [expect_cons, ok_bind]
  -- The parameters: none when `)` follows the `(`, and read otherwise.
  refine bind_reads (fun v => v.1.1.map eraseParam = PS.map paramTree ∧ v.1.2.isSome = f.variadic ∧
    v.2.1.map (·.tok) = .rparen :: ((if f.results.isEmpty = true then [] else
      .arrow :: [Tok.comma].intercalate (RS.map resultToks)) ++
      .lbrace :: (Block.tokensList f.body.blocks ++ .rbrace :: rest))) ?_ ?_
  · split
    case h_1 =>
      by_cases hne : PS ≠ [] ∨ f.variadic = true
      · exfalso
        rcases PS with _ | ⟨q, qs⟩
        · obtain hv : f.variadic = true := hne.resolve_left (by simp)
          simp [paramsToks, ellipsisToks, hv] at h
        · simp [paramsToks, paramToks, defTokens] at h
      · simp only [not_or, ne_eq, Classical.not_not, Bool.not_eq_true] at hne
        obtain ⟨hp, hv⟩ := hne
        simp only [paramsToks, hp, List.map_nil, List.intercalate_nil, List.isEmpty_nil,
          ellipsisToks, hv, Bool.false_eq_true, ite_false, List.nil_append, List.append_nil] at h
        exact ⟨_, rfl, by simp [hp], by simp [hv], h⟩
    case h_2 hnr =>
      by_cases hne : PS ≠ [] ∨ f.variadic = true
      · obtain ⟨sps, r, hD, hP, h⟩ := readParams_reads hne hPS _ _ h (by simp)
        simp only [Prod.mk.injEq] at hP
        exact ⟨(sps, r), hD, hP.1, hP.2, h⟩
      · simp only [not_or, ne_eq, Classical.not_not, Bool.not_eq_true] at hne
        obtain ⟨hp, hv⟩ := hne
        simp only [paramsToks, hp, List.map_nil, List.intercalate_nil, List.isEmpty_nil,
          ellipsisToks, hv, Bool.false_eq_true, ite_false, List.nil_append, List.append_nil] at h
        take_tok h
        exact (hnr _ _ _ rfl HEq.rfl).elim
  rintro ⟨⟨sps, variadic⟩, ⟨r₂, hr₂⟩⟩ ⟨hP, hV, h⟩
  take_tok h
  simp only [expect_cons, ok_bind]
  -- The results: none when `{` follows the `)`, and read after `->` otherwise.
  refine bind_reads (fun v => v.1.map eraseResult = RS.map (fun r => ((r.1, .zero), r.2)) ∧
    v.2.1.map (·.tok) = .lbrace :: (Block.tokensList f.body.blocks ++ .rbrace :: rest)) ?_ ?_
  · split
    case h_1 =>
      rcases RS with _ | ⟨r, rs⟩
      · simp [hRe.mp rfl] at h
      have hnr : f.results.isEmpty = false := by
        cases hfr : f.results
        · exact absurd (hRe.mpr hfr) (by simp)
        · rfl
      simp only [hnr, Bool.false_eq_true, ite_false, List.map_cons, intercalate_cons,
        flatMap_comma_map, List.cons_append, List.append_assoc, List.cons.injEq, true_and] at h
      obtain ⟨⟨a, q⟩, ⟨r₁, hr₁⟩, hT, hT', h⟩ := readResult_reads (hRS r (by simp)) _ _ h
        (head?_append _ (by cases rs <;> simp [Tok.startsAttr]) (by simp [Tok.startsAttr]))
      obtain ⟨more, r', hM, hM', h⟩ := Reads.more (stop := fun t => t.startsAttr = false ∧
        t ≠ .lparen) (by simp [Tok.startsAttr]) (stop' := (· = .lbrace))
        (fun t ht => by subst ht; simp [Tok.startsAttr])
        (fun y hy => readResult_reads (hRS y (by simp [hy]))) _ _ h (by simp)
      simp only [hT, ok_bind, hM, After.then, After.next]
      exact ⟨_, rfl, by simp [hT', hM'], h⟩
    case h_2 hne =>
      by_cases hr : f.results.isEmpty = true
      · simp only [hr, ↓reduceIte, List.nil_append] at h
        have : RS = [] := hRe.mpr (List.isEmpty_iff.mp hr)
        exact ⟨_, rfl, by simp [this], h⟩
      · simp only [hr, Bool.false_eq_true, ↓reduceIte, List.cons_append] at h
        take_tok h
        exact (hne _ _ _ rfl HEq.rfl).elim
  rintro ⟨srs, ⟨r₄, hr₄⟩⟩ ⟨hR, h⟩
  -- No attributes after the results, since `{` follows.
  replace h := readAttrs_reads [] _ _ h (by simp [Tok.startsAttr])
  obtain ⟨attrs, ⟨r₅, hr₅⟩, hA, hA', h⟩ := h
  obtain rfl : attrs = [] := List.map_eq_nil_iff.mp hA'
  take_tok h
  simp only [hA, ok_bind, expect_cons]
  -- The body: blocks, since a label or `}` follows the `{`.
  refine bind_reads (fun v => (∃ bs, v.1 = .blocks bs ∧
    SBlock.eraseList bs = Block.treeList f.body.blocks) ∧ v.2.1.map (·.tok) = .rbrace :: rest) ?_ ?_
  · split
    case h_1 w q tl _ _ =>
      exact absurd (head_blocks f.body.blocks (.rbrace :: rest) (fun t => ∀ w, t ≠ .word w)
        (by simp) (by simp) (.word w) (by rw [← h]; rfl) w) (by simp)
    case h_2 =>
      obtain ⟨sbs, r, hB, hB', h⟩ := Block.readsList f.body.blocks hblk _ _ h (by simp)
      simp only [hB, ok_bind]
      exact ⟨_, rfl, ⟨sbs, rfl, hB'⟩, h⟩
  clear h hblk
  rintro ⟨body, ⟨r₇, hr₇⟩⟩ ⟨⟨sbs, rfl, hB'⟩, h⟩
  take_tok h
  simp only [expect_cons, ok_bind]
  refine ⟨_, _, rfl, ?_, h⟩
  obtain ⟨hP₁, hP₂⟩ := params_read hP
  obtain ⟨hR₁, hR₂, hR₃⟩ := results_read hR
  have hRS₂ : RS.map (·.2) = f.resultAttrsAll := by
    subst hRSd
    simp only [List.map_map, Function.comp_def]
    exact List.map_snd_zip (by simp [Func.resultAttrsAll])
  have hRS₁ : RS.map (fun r => (r.1, TextPos.zero)) = f.results.map (tyAttr ·, TextPos.zero) := by
    subst hRSd
    have := congrArg (List.map (tyAttr ·, TextPos.zero)) (List.map_fst_zip hlr)
    simpa [List.map_map, Function.comp_def] using this
  subst hPSd
  simp only [SItem.erase, SBody.erase, Func.tree, SItem.mk.injEq, true_and, List.append_nil]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, congrArg SBody.blocks hB'⟩
  · rw [hP₁, List.map_fst_zip hlp]
  · rw [hP₂, List.map_snd_zip (by simp [Func.paramAttrsAll])]
  · cases variadic <;> cases hf : f.variadic <;> simp_all
  · rw [hR₁, hRS₁]
  · rw [hR₂, hRS₂]
  · rw [hR₃, hRS₂]

/-- `readItem` reads the tokens of a function after its kind, `func`, as the
function's tree, when each type it writes is written as a type. -/
theorem Func.reads (f : Func d) (ht : ∀ t ∈ f.types, (tyAttr t).IsType) (p : TextPos) :
    Reads (readItem "func" p) SItem.erase f.tree f.tokens.tail (fun _ => True) :=
  Func.readsAs "func" f ht p

/-- The tokens of attributes, then `{`, start with a token that starts an
attribute, or with the `{`. -/
theorem head_attrs (as : List Attr) (r : List Tok) :
    ∀ t ∈ (as.flatMap Attr.tokens ++ .lbrace :: r).head?, t.startsAttr = true ∨ t = .lbrace := by
  cases as with
  | nil => simp
  | cons a _ => cases a <;> simp [Attr.tokens, Tok.startsAttr]

/-- `readItem` reads the tokens of an item of a dialect's kind after its
kind as the item's tree, when each type it writes is written as a type. Its
attributes are read after its last result, as if that result carried them,
or after its `)` when it has no results. -/
theorem DialectItem.reads (i : DialectItem d) (ht : ∀ t ∈ i.types, (tyAttr t).IsType)
    (p : TextPos) : Reads (readItem i.kind p) SItem.erase i.tree i.tokens.tail (fun _ => True) := by
  obtain ⟨kind, name, params, results, attrs⟩ := i
  have hres : ∀ t ∈ results, (tyAttr t).IsType := fun t h => ht t (List.mem_append_right _ h)
  have hpar : ∀ x ∈ params, (tyAttr x.2).IsType := fun x hx =>
    ht x.2 (List.mem_append_left _ (List.mem_map_of_mem hx))
  have hA := head_attrs attrs
  clear ht
  let PS : List ((Name × d.Ty) × List Attr) := params.map (·, [])
  have hPS : ∀ q ∈ PS, (tyAttr q.1.2).IsType := fun q hq => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
    exact hpar x hx
  have hPt : defsTokens params = paramsToks PS false := by
    simp [PS, defsTokens, paramsToks, ellipsisToks, paramToks, List.map_map, Function.comp_def]
  obtain ⟨RS, hRSd⟩ : ∃ RS, lastAttrs (results.map tyAttr) attrs = RS := ⟨_, rfl⟩
  have hRS : ∀ r ∈ RS, r.1.IsType := fun r hr => by
    have hm : r.1 ∈ (lastAttrs (results.map tyAttr) attrs).map (·.1) :=
      List.mem_map_of_mem (hRSd ▸ hr)
    rw [lastAttrs_fst] at hm
    obtain ⟨t, ht, he⟩ := List.mem_map.mp hm
    exact he ▸ hres t ht
  have hRt : (if results.isEmpty = true then [] else
      .arrow :: [Tok.comma].intercalate (results.map (tyAttr · |>.tokens))) ++
        attrs.flatMap Attr.tokens =
      (if results.isEmpty = true then [] else .arrow :: [Tok.comma].intercalate (RS.map resultToks)) ++
        ((if results.isEmpty = true then attrs else []).flatMap Attr.tokens) := by
    rcases results with _ | ⟨t, ts⟩
    · simp
    · subst hRSd
      have := lastAttrs_tokens Attr.tokens attrs (xs := (t :: ts).map tyAttr) (by simp)
      simp only [List.map_map, Function.comp_def] at this
      simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, List.flatMap_nil,
        List.append_nil, List.cons_append, this]
      rfl
  rintro ts rest h -
  simp only [DialectItem.tokens, List.tail_cons, List.cons_append, List.append_assoc,
    List.nil_append, hPt] at h
  rw [← List.append_assoc, hRt, List.append_assoc] at h
  take_tok h
  take_tok h
  rw [readItem.eq_1]
  simp only [expect_cons, ok_bind]
  -- The parameters: none when `)` follows the `(`, and read otherwise.
  refine bind_reads (fun v => v.1.1.map eraseParam = PS.map paramTree ∧ v.1.2 = none ∧
    v.2.1.map (·.tok) = .rparen :: ((if results.isEmpty = true then [] else
      .arrow :: [Tok.comma].intercalate (RS.map resultToks)) ++
      ((if results.isEmpty = true then attrs else []).flatMap Attr.tokens ++
        .lbrace :: .rbrace :: rest))) ?_ ?_
  · split
    case h_1 =>
      rcases params with _ | ⟨x, xs⟩
      · simp only [PS, paramsToks, List.map_nil, List.intercalate_nil, ellipsisToks,
          Bool.false_eq_true, ite_false, List.append_nil, List.nil_append] at h
        exact ⟨_, rfl, rfl, rfl, h⟩
      · simp [PS, paramsToks, paramToks, defTokens] at h
    case h_2 hne =>
      rcases params with _ | ⟨x, xs⟩
      · simp only [PS, paramsToks, List.map_nil, List.intercalate_nil, ellipsisToks,
          Bool.false_eq_true, ite_false, List.append_nil, List.nil_append] at h
        take_tok h
        exact (hne _ _ _ rfl HEq.rfl).elim
      · obtain ⟨sps, r, hD, hP, h⟩ := readParams_reads (.inl (by simp [PS])) hPS _ _ h (by simp)
        simp only [Prod.mk.injEq, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hP
        exact ⟨(sps, r), hD, hP.1, hP.2, h⟩
  clear h hpar
  rintro ⟨⟨sps, variadic⟩, ⟨r₂, hr₂⟩⟩ ⟨hP, rfl, h⟩
  take_tok h
  simp only [expect_cons, ok_bind]
  -- The results: none when no `->` follows the `)`, and read after `->` otherwise.
  refine bind_reads (fun v => v.1.map eraseResult = RS.map (fun r => ((r.1, .zero), r.2)) ∧
    v.2.1.map (·.tok) = (if results.isEmpty = true then attrs else []).flatMap Attr.tokens ++
      .lbrace :: .rbrace :: rest) ?_ ?_
  · split
    case h_1 q tl =>
      rcases results with _ | ⟨t, ts⟩
      · simp only [List.isEmpty_nil, ↓reduceIte, List.nil_append] at h
        have := hA (.rbrace :: rest) .arrow (by rw [← h]; rfl)
        simp [Tok.startsAttr] at this
      obtain ⟨r, rs, hRc⟩ : ∃ r rs, RS = r :: rs := by
        rcases hR : RS with _ | ⟨r, rs⟩
        · rw [← hRSd] at hR; cases ts <;> simp [lastAttrs] at hR
        · exact ⟨r, rs, rfl⟩
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, hRc, List.map_cons,
        intercalate_cons, flatMap_comma_map, List.cons_append, List.append_assoc, List.cons.injEq,
        true_and, List.flatMap_nil, List.nil_append] at h
      obtain ⟨⟨a, q'⟩, ⟨r₁, hr₁⟩, hT, hT', h⟩ := readResult_reads (hRS r (by simp [hRc])) _ _ h
        (head?_append _ (by cases rs <;> simp [Tok.startsAttr]) (by simp [Tok.startsAttr]))
      obtain ⟨more, r', hM, hM', h⟩ := Reads.more (stop := fun t => t.startsAttr = false ∧
        t ≠ .lparen) (by simp [Tok.startsAttr]) (stop' := (· = .lbrace))
        (fun t ht => by subst ht; simp [Tok.startsAttr])
        (fun y hy => readResult_reads (hRS y (by simp [hRc, hy]))) _ _ h (by simp)
      simp only [hT, ok_bind, hM, After.then, After.next]
      exact ⟨_, rfl, by simp [hRc, hT', hM'], by simpa using h⟩
    case h_2 hne =>
      rcases results with _ | ⟨t, ts⟩
      · simp only [List.isEmpty_nil, ↓reduceIte, List.nil_append] at h
        have : RS = [] := by rw [← hRSd]; rfl
        exact ⟨_, rfl, by simp [this], h⟩
      · simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.cons_append] at h
        take_tok h
        exact (hne _ _ _ rfl HEq.rfl).elim
  clear h hres
  rintro ⟨srs, ⟨r₄, hr₄⟩⟩ ⟨hR, h⟩
  -- The attributes after the `)`, when there are no results.
  replace h := readAttrs_reads (if results.isEmpty = true then attrs else []) _ _ h
    (by simp [Tok.startsAttr])
  obtain ⟨sas, ⟨r₅, hr₅⟩, hS, hS', h⟩ := h
  take_tok h
  simp only [hS, ok_bind, expect_cons]
  -- The body: no blocks, since `}` follows the `{`.
  refine bind_reads (fun v => v.1 = .blocks [] ∧ v.2.1.map (·.tok) = .rbrace :: rest) ?_ ?_
  · split
    case h_1 w q tl _ _ => simp at h
    case h_2 =>
      obtain ⟨sbs, r, hB, hB', h⟩ := Block.readsList ([] : List (Block d))
        (by simp [Block.allBlocks]) _ _ h (by simp)
      simp only [hB, ok_bind]
      obtain rfl : sbs = [] := by
        cases sbs with
        | nil => rfl
        | cons b _ => obtain ⟨⟩ := b; simp [SBlock.eraseList, Block.treeList] at hB'
      exact ⟨_, rfl, rfl, h⟩
  clear h
  rintro ⟨body, ⟨r₇, hr₇⟩⟩ ⟨rfl, h⟩
  take_tok h
  simp only [expect_cons, ok_bind]
  refine ⟨_, _, rfl, ?_, h⟩
  obtain ⟨hP₁, hP₂⟩ := params_read hP
  obtain ⟨hR₁, hR₂, hR₃⟩ := results_read hR
  have hRS₁ : RS.map (·.1) = results.map tyAttr := by rw [← hRSd, lastAttrs_fst]
  have hRS₂ : (RS.map (·.2)).dropLast = results.dropLast.map fun _ => [] := by
    rw [← hRSd, ← List.map_dropLast, lastAttrs_dropLast]
    simp [← List.map_dropLast, Function.comp_def]
  simp only [SItem.erase, SBody.erase, SBlock.eraseList, DialectItem.tree, SItem.mk.injEq,
    true_and, List.map_append]
  refine ⟨?_, ?_, rfl, ?_, ?_, ?_⟩
  · rw [hP₁]; simp [PS, List.map_map, Function.comp_def]
  · rw [hP₂]; simp [PS, List.map_map, Function.comp_def, attrsTree]
  · rw [hR₁]
    have := congrArg (List.map (·, TextPos.zero)) hRS₁
    simpa [List.map_map, Function.comp_def] using this
  · rw [hR₂, hRS₂]; simp [List.map_map, Function.comp_def, attrsTree]
  · rw [hR₃, map_eraseAt, hS']
    rcases results with _ | ⟨t, ts⟩
    · have : RS = [] := by rw [← hRSd]; rfl
      simp [this, attrsTree]
    · rw [← hRSd, List.getLast?_map, lastAttrs_getLast attrs (by simp)]
      simp [attrsTree]

end Fir
