import Fir.Text.ReadBlocks

/-!
# Reading a printed function

A function's tokens after its kind read back as its tree, whatever follows
them. The reader of an item chooses on the next token at three places: it
reads the parameters as definitions when a value follows the `(`, and as
none when `)` does; the results after `->` when one follows the `)`; and
the body as items when a word follows the `{`, and as blocks otherwise. A
function's parameters, results and blocks decide which way the printed
tokens go, and the proof follows that way and rules out the other. A lemma
on one step followed by another lets it prove each part on its own: what
the part reads, then what the rest of the reader does with it.

The tokens after the `{` start with a block's label, or are the `}` when
the function has no block, and never with a word. So the reader of an item
reads every printed body as blocks, the empty one included, which is how
the tree of a function writes it. No attribute is read, since a `{` follows
the results.

An item of a dialect's kind reads back the same way, with its attributes
read between its results and its `{`, and its empty body read as no blocks
(ADR-2026-11-10-2224). Its attributes start with a word, a number, a string
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

/-- `readItem` reads the tokens of a function after its kind, `func`, as the
function's tree, when each type it writes is written as a type. -/
theorem Func.reads (f : Func d) (ht : ∀ t ∈ f.types, (tyAttr t).IsType) (p : TextPos) :
    Reads (readItem "func" p) SItem.erase f.tree f.tokens.tail (fun _ => True) := by
  obtain ⟨name, params, results, ⟨_, blocks⟩⟩ := f
  have hres : ∀ t ∈ results, (tyAttr t).IsType := fun t h => ht t (List.mem_append_left _ h)
  have hpar : ∀ x ∈ params, (tyAttr x.2).IsType := fun x hx =>
    ht x.2 (List.mem_append_right _ (List.mem_map_of_mem (List.mem_append_left _ hx)))
  have hblk : ∀ b ∈ Block.allBlocks blocks, ∀ x ∈ b.defs, (tyAttr x.2).IsType :=
    fun b hb x hx => ht x.2 (List.mem_append_right _ (List.mem_map_of_mem
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨b, hb, hx⟩))))
  clear ht
  rintro ts rest h -
  simp only [Func.tokens, List.tail_cons, List.cons_append, List.append_assoc,
    List.nil_append] at h
  take_tok h
  take_tok h
  rw [readItem.eq_1]
  simp only [expect_cons, ok_bind]
  -- The parameters: none when `)` follows the `(`, and definitions otherwise.
  refine bind_reads (fun v => v.1.map SDef.erase = params.map defTree ∧
    v.2.1.map (·.tok) = .rparen :: ((if results.isEmpty = true then [] else
      .arrow :: [Tok.comma].intercalate (results.map (tyAttr · |>.tokens))) ++
      .lbrace :: (Block.tokensList blocks ++ .rbrace :: rest))) ?_ ?_
  · split
    case h_1 =>
      rcases params with _ | ⟨x, xs⟩
      · simp only [defsTokens, List.map_nil, List.intercalate_nil, List.nil_append] at h
        exact ⟨_, rfl, rfl, h⟩
      · simp [defsTokens, intercalate_cons, defTokens] at h
    case h_2 hne =>
      rcases params with _ | ⟨x, xs⟩
      · simp only [defsTokens, List.map_nil, List.intercalate_nil, List.nil_append] at h
        take_tok h
        exact (hne _ _ _ rfl HEq.rfl).elim
      · obtain ⟨sps, r, hD, hP, h⟩ := readDefs_reads (List.cons_ne_nil x xs) hpar _ _ h (by simp)
        exact ⟨(sps, r), hD, hP, h⟩
  clear h hpar
  rintro ⟨sps, ⟨r₂, hr₂⟩⟩ ⟨hP, h⟩
  take_tok h
  simp only [expect_cons, ok_bind]
  -- The results: none when `{` follows the `)`, and types after `->` otherwise.
  refine bind_reads (fun v => v.1.map eraseAt = results.map (tyAttr ·, TextPos.zero) ∧
    v.2.1.map (·.tok) = .lbrace :: (Block.tokensList blocks ++ .rbrace :: rest)) ?_ ?_
  · split
    case h_1 =>
      rcases results with _ | ⟨t, ts⟩
      · simp at h
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.map_cons,
        intercalate_cons, flatMap_comma_map, List.cons_append, List.append_assoc, List.cons.injEq,
        true_and] at h
      replace h := readType_reads (hres t (.head _)) _ _ h
        (head?_append _ (by cases ts <;> simp) (by simp))
      obtain ⟨⟨a, q⟩, ⟨r₁, hr₁⟩, hT, hT', h⟩ := h
      replace h := Reads.more (stop := (· ≠ .lparen)) (by decide)
        (stop' := (· = .lbrace)) (fun t ht => by subst ht; decide)
        (fun y hy => readType_reads (hres y (.tail _ hy))) _ _ h (by simp)
      obtain ⟨more, r, hM, hM', h⟩ := h
      simp only [hT, ok_bind, hM, After.then, After.next]
      exact ⟨_, rfl, by simp [hT', hM'], h⟩
    case h_2 hne =>
      rcases results with _ | ⟨t, ts⟩
      · simp only [List.isEmpty_nil, ↓reduceIte, List.nil_append] at h
        exact ⟨_, rfl, rfl, h⟩
      · simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.cons_append] at h
        take_tok h
        exact (hne _ _ _ rfl HEq.rfl).elim
  clear h hres
  rintro ⟨srs, ⟨r₄, hr₄⟩⟩ ⟨hR, h⟩
  -- No attributes, since `{` follows.
  replace h := readAttrs_reads [] _ _ h (by simp [Tok.startsAttr])
  obtain ⟨attrs, ⟨r₅, hr₅⟩, hA, hA', h⟩ := h
  obtain rfl : attrs = [] := List.map_eq_nil_iff.mp hA'
  take_tok h
  simp only [hA, ok_bind, expect_cons]
  -- The body: blocks, since a label or `}` follows the `{`.
  refine bind_reads (fun v => (∃ bs, v.1 = .blocks bs ∧ SBlock.eraseList bs = Block.treeList blocks) ∧
    v.2.1.map (·.tok) = .rbrace :: rest) ?_ ?_
  · split
    case h_1 w q tl _ _ =>
      exact absurd (head_blocks blocks (.rbrace :: rest) (fun t => ∀ w, t ≠ .word w) (by simp)
        (by simp) (.word w) (by rw [← h]; rfl) w) (by simp)
    case h_2 =>
      obtain ⟨sbs, r, hB, hB', h⟩ := Block.readsList blocks hblk _ _ h (by simp)
      simp only [hB, ok_bind]
      exact ⟨_, rfl, ⟨sbs, rfl, hB'⟩, h⟩
  clear h hblk
  rintro ⟨body, ⟨r₇, hr₇⟩⟩ ⟨⟨sbs, rfl, hB'⟩, h⟩
  take_tok h
  simp only [expect_cons, ok_bind]
  exact ⟨_, _, rfl, by simp [SItem.erase, SBody.erase, Func.tree, hP, hR, hB'], h⟩

/-- The tokens of attributes, then `{`, start with a token that starts an
attribute, or with the `{`. -/
theorem head_attrs (as : List Attr) (r : List Tok) :
    ∀ t ∈ (as.flatMap Attr.tokens ++ .lbrace :: r).head?, t.startsAttr = true ∨ t = .lbrace := by
  cases as with
  | nil => simp
  | cons a _ => cases a <;> simp [Attr.tokens, Tok.startsAttr]

/-- `readItem` reads the tokens of an item of a dialect's kind after its
kind as the item's tree, when each type it writes is written as a type. -/
theorem DialectItem.reads (i : DialectItem d) (ht : ∀ t ∈ i.types, (tyAttr t).IsType)
    (p : TextPos) : Reads (readItem i.kind p) SItem.erase i.tree i.tokens.tail (fun _ => True) := by
  obtain ⟨kind, name, params, results, attrs⟩ := i
  have hres : ∀ t ∈ results, (tyAttr t).IsType := fun t h => ht t (List.mem_append_right _ h)
  have hpar : ∀ x ∈ params, (tyAttr x.2).IsType := fun x hx =>
    ht x.2 (List.mem_append_left _ (List.mem_map_of_mem hx))
  have hA := head_attrs attrs
  clear ht
  rintro ts rest h -
  simp only [DialectItem.tokens, List.tail_cons, List.cons_append, List.append_assoc,
    List.nil_append] at h
  take_tok h
  take_tok h
  rw [readItem.eq_1]
  simp only [expect_cons, ok_bind]
  -- The parameters: none when `)` follows the `(`, and definitions otherwise.
  refine bind_reads (fun v => v.1.map SDef.erase = params.map defTree ∧
    v.2.1.map (·.tok) = .rparen :: ((if results.isEmpty = true then [] else
      .arrow :: [Tok.comma].intercalate (results.map (tyAttr · |>.tokens))) ++
      (attrs.flatMap Attr.tokens ++ .lbrace :: .rbrace :: rest))) ?_ ?_
  · split
    case h_1 =>
      rcases params with _ | ⟨x, xs⟩
      · simp only [defsTokens, List.map_nil, List.intercalate_nil, List.nil_append] at h
        exact ⟨_, rfl, rfl, h⟩
      · simp [defsTokens, intercalate_cons, defTokens] at h
    case h_2 hne =>
      rcases params with _ | ⟨x, xs⟩
      · simp only [defsTokens, List.map_nil, List.intercalate_nil, List.nil_append] at h
        take_tok h
        exact (hne _ _ _ rfl HEq.rfl).elim
      · obtain ⟨sps, r, hD, hP, h⟩ := readDefs_reads (List.cons_ne_nil x xs) hpar _ _ h (by simp)
        exact ⟨(sps, r), hD, hP, h⟩
  clear h hpar
  rintro ⟨sps, ⟨r₂, hr₂⟩⟩ ⟨hP, h⟩
  take_tok h
  simp only [expect_cons, ok_bind]
  -- The results: none when no `->` follows the `)`, and types after `->` otherwise.
  refine bind_reads (fun v => v.1.map eraseAt = results.map (tyAttr ·, TextPos.zero) ∧
    v.2.1.map (·.tok) = attrs.flatMap Attr.tokens ++ .lbrace :: .rbrace :: rest) ?_ ?_
  · split
    case h_1 q tl =>
      rcases results with _ | ⟨t, ts⟩
      · simp only [List.isEmpty_nil, ↓reduceIte, List.nil_append] at h
        have := hA (.rbrace :: rest) .arrow (by rw [← h]; rfl)
        simp [Tok.startsAttr] at this
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.map_cons,
        intercalate_cons, flatMap_comma_map, List.cons_append, List.append_assoc, List.cons.injEq,
        true_and] at h
      have hnp : ∀ u ∈ (attrs.flatMap Attr.tokens ++ .lbrace :: .rbrace :: rest).head?,
          u ≠ .lparen := fun u hu => by
        rcases hA _ u hu with hu | rfl
        · rintro rfl; simp [Tok.startsAttr] at hu
        · decide
      replace h := readType_reads (hres t (.head _)) _ _ h
        (head?_append _ (by cases ts <;> simp) hnp)
      obtain ⟨⟨a, q'⟩, ⟨r₁, hr₁⟩, hT, hT', h⟩ := h
      replace h := Reads.more (stop := (· ≠ .lparen)) (by decide)
        (stop' := fun u => u ≠ .lparen ∧ u ≠ .comma) (fun u hu => hu)
        (fun y hy => readType_reads (hres y (.tail _ hy))) _ _ h fun u hu => by
          refine ⟨hnp u hu, ?_⟩
          rcases hA _ u hu with hu | rfl
          · rintro rfl; simp [Tok.startsAttr] at hu
          · decide
      obtain ⟨more, r, hM, hM', h⟩ := h
      simp only [hT, ok_bind, hM, After.then, After.next]
      exact ⟨_, rfl, by simp [hT', hM'], h⟩
    case h_2 hne =>
      rcases results with _ | ⟨t, ts⟩
      · simp only [List.isEmpty_nil, ↓reduceIte, List.nil_append] at h
        exact ⟨_, rfl, rfl, h⟩
      · simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.cons_append] at h
        take_tok h
        exact (hne _ _ _ rfl HEq.rfl).elim
  clear h hres
  rintro ⟨srs, ⟨r₄, hr₄⟩⟩ ⟨hR, h⟩
  -- The attributes, before the `{`.
  replace h := readAttrs_reads attrs _ _ h (by simp [Tok.startsAttr])
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
  have hS'' : sas.map eraseAt = attrs.map (·, TextPos.zero) := by
    rw [← hS']; simp [eraseAt]
  simp [SItem.erase, SBody.erase, SBlock.eraseList, DialectItem.tree, hP, hR, hS'']

end Fir
