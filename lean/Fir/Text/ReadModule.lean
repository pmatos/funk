import Fir.Text.ReadFunc
import Fir.Text.ReadTable

/-!
# Reading a printed module

A module's dialect set reads back first, then its items before the word
`locs`, which starts its location table, and the table before `eof`. A
function reads back as the previous sections show. A nested module reads
back the same way as a module, its dialect set and then its items, before
the `}` that closes its body; the reader of items and the reader of an item
are proved together, by induction on the items.

The result is the grammar step: on any tokens that hold the module's
tokens, then `eof`, at any positions, the reader of a module gives a tree
that is the module's tree once its positions are erased. It needs only that
each type the module writes is written as a type, and that its location
table is within the limits; the names of its dialect set are read as any
words. A well-formed module has both, so with lexing
printed text the first two steps of the parser read its printed text as its
tree, and so do they for a valid module. The last step decodes that tree,
and gives the module back, in the sections that follow.
-/

namespace Fir

open Text

variable {d : Dialect} [DialectText d]

/-- `readDialectName` reads a word as the name it is, before any token. -/
theorem readDialectName_reads (x : Name) :
    Reads readDialectName id x [.word x] (fun _ => True) := by
  intro ts rest h _
  take_tok h
  exact ⟨x, _, rfl, rfl, h⟩

/-- `readDialects` reads the tokens of a module's dialect set as the set,
before any token but a comma and the word `dialects`. -/
theorem readDialects_reads (ns : List Name) :
    Reads readDialects id ns (dialectsTokens ns) (fun t => t ≠ .comma ∧ t ≠ .word "dialects") := by
  intro ts rest h hs
  cases ns with
  | nil =>
    simp only [dialectsTokens, List.isEmpty_nil, ite_true, List.nil_append] at h
    rw [readDialects.eq_2 _ fun p ts' he => not_cons_of_head h (fun u hu => (hs u hu).2) p ts' he]
    exact ⟨[], _, rfl, rfl, h⟩
  | cons n ns =>
    simp only [dialectsTokens, List.isEmpty_cons, Bool.false_eq_true, ite_false, List.map_cons,
      intercalate_cons, List.cons_append, List.nil_append] at h
    take_tok h
    take_tok h
    have hm := Reads.more (item := readDialectName) (f := id) (g := id)
      (toks := fun x => [Tok.word x]) (stop := fun _ => True) trivial
      (stop' := fun t => t ≠ .comma ∧ t ≠ .word "dialects") (fun t ht => ⟨trivial, ht.1⟩) (xs := ns) (fun x _ => readDialectName_reads x)
    obtain ⟨xs, ⟨r, hr⟩, h₁, h₂, h₃⟩ := hm _ rest
      (by simpa [List.flatMap_map] using h) hs
    rw [readDialects.eq_1]
    simp only [readDialectName, ok_bind, h₁]
    exact ⟨_, _, rfl, by simpa using h₂, h₃⟩

/-- The word that starts an item: its kind. -/
def Item.kind : Item d → String
  | .func _ => "func"
  | .module .. => "module"

theorem Item.tokens_eq (i : Item d) : i.tokens = .word i.kind :: i.tokens.tail := by
  cases i <;> rfl

/-- The tokens of items, then tokens that start with `P`, start with a word
that is the kind of an item, or with `P`. -/
theorem head_items (is : List (Item d)) (rest : List Tok) (P : Tok → Prop)
    (hk : P (.word "func") ∧ P (.word "module")) (hr : ∀ t ∈ rest.head?, P t) :
    ∀ t ∈ (Item.tokensList is ++ rest).head?, P t := by
  cases is with
  | nil => simpa [Item.tokensList] using hr
  | cons i _ => cases i <;> simp [Item.tokensList, Item.tokens, Func.tokens, hk]

mutual
/-- Each type that an item writes is written as a type, at any depth. -/
def Item.TypesWritable : Item d → Prop
  | .func f => ∀ t ∈ f.types, (tyAttr t).IsType
  | .module _ _ is => Item.TypesWritableList is

/-- Each type that these items write is written as a type. -/
def Item.TypesWritableList : List (Item d) → Prop
  | [] => True
  | i :: is => i.TypesWritable ∧ Item.TypesWritableList is
end

theorem Item.typesWritableList_iff : ∀ is : List (Item d),
    Item.TypesWritableList is ↔ ∀ i ∈ is, i.TypesWritable
  | [] => by simp [Item.TypesWritableList]
  | i :: is => by simp [Item.TypesWritableList, Item.typesWritableList_iff is]

/-- What ends a list of items: the word `locs` at the top of a module, and
`}` in the body of an item. -/
def itemsEnd (top : Bool) (t : Tok) : Prop := if top then t = .word "locs" else t = .rbrace

mutual
/-- `readItem` reads the tokens of an item after its kind as the item's
tree, when each type it writes is written as a type. -/
theorem Item.reads : ∀ i : Item d, i.TypesWritable → ∀ p,
    Reads (readItem i.kind p) SItem.erase i.tree i.tokens.tail (fun _ => True)
  | .func f, ht, p => Func.reads f ht p
  | .module name ds is, ht, p => by
    have his := Item.readsList false is ht
    rintro ts rest h -
    simp only [Item.tokens, List.tail_cons, List.cons_append, List.append_assoc] at h
    take_tok h
    take_tok h
    rw [readItem.eq_1]
    simp only [expect_cons, ok_bind]
    -- No parameters, since `)` follows the `(`.
    refine bind_reads (fun v => v.1 = [] ∧ v.2.1.map (·.tok) = .rparen :: .lbrace ::
      (dialectsTokens ds ++ (Item.tokensList is ++ .rbrace :: rest))) ?_ ?_
    · split
      case h_1 => exact ⟨_, rfl, rfl, h⟩
      case h_2 hne =>
        take_tok h
        exact (hne _ _ _ rfl HEq.rfl).elim
    rintro ⟨sps, ⟨r₂, hr₂⟩⟩ ⟨rfl, h⟩
    take_tok h
    simp only [expect_cons, ok_bind]
    -- No results, since `{` follows the `)`.
    refine bind_reads (fun v => v.1 = [] ∧ v.2.1.map (·.tok) = .lbrace ::
      (dialectsTokens ds ++ (Item.tokensList is ++ .rbrace :: rest))) ?_ ?_
    · split
      case h_1 => simp at h
      case h_2 => exact ⟨_, rfl, rfl, h⟩
    rintro ⟨srs, ⟨r₄, hr₄⟩⟩ ⟨rfl, h⟩
    -- No attributes, since `{` follows.
    replace h := readAttrs_reads [] _ _ h (by simp [Tok.startsAttr])
    obtain ⟨attrs, ⟨r₅, hr₅⟩, hA, hA', h⟩ := h
    obtain rfl : attrs = [] := List.map_eq_nil_iff.mp hA'
    take_tok h
    simp only [hA, ok_bind, expect_cons]
    -- The body: no blocks when `}` follows the `{`, and a dialect set and
    -- items otherwise, which start with a word.
    refine bind_reads (fun v => v.1.erase = moduleBody ds (Item.treeList is) ∧
      v.2.1.map (·.tok) = .rbrace :: rest) ?_ ?_
    · by_cases he : ds = [] ∧ is = []
      · obtain ⟨rfl, rfl⟩ := he
        simp only [dialectsTokens, List.isEmpty_nil, ite_true, Item.tokensList,
          List.nil_append] at h
        split
        case h_1 w q tl _ _ => simp at h
        case h_2 =>
          obtain ⟨sbs, r, hB, hB', h⟩ := Block.readsList ([] : List (Block d))
            (by simp [Block.allBlocks]) _ _ h (by simp)
          simp only [hB, ok_bind]
          refine ⟨_, rfl, ?_, h⟩
          simp only [SBody.erase, moduleBody, Item.treeList, List.isEmpty_nil, and_self,
            ite_true]
          simpa [Block.treeList] using hB'
      · obtain ⟨w, L, hL⟩ : ∃ w L,
            dialectsTokens ds ++ (Item.tokensList is ++ .rbrace :: rest) = .word w :: L := by
          rcases ds with _ | ⟨x, xs⟩
          · rcases is with _ | ⟨i, is⟩
            · exact absurd ⟨rfl, rfl⟩ he
            · cases i <;> simp [dialectsTokens, Item.tokensList, Item.tokens, Func.tokens]
          · simp [dialectsTokens]
        rw [hL] at h
        obtain ⟨q, tl, rfl, h⟩ := map_tok_cons h
        dsimp only
        · have h' : (⟨.word w, q⟩ :: tl : List Token).map (·.tok) =
              dialectsTokens ds ++ (Item.tokensList is ++ .rbrace :: rest) := by
            rw [hL]; simp [h]
          have hst : ∀ t ∈ (Item.tokensList is ++ .rbrace :: rest).head?,
              t ≠ .comma ∧ t ≠ .word "dialects" :=
            head_items _ _ _ (by simp) (by simp)
          obtain ⟨ns, ⟨r, hr⟩, hD, hD', h⟩ := readDialects_reads ds _ _ h' hst
          obtain ⟨sis, ⟨r', hr'⟩, hI, hI', h⟩ := his r _ h (by simp [itemsEnd])
          simp only [hD, ok_bind, hI]
          refine ⟨_, rfl, ?_, h⟩
          obtain rfl : ns = ds := hD'
          have hne : ¬(ns.isEmpty = true ∧ (Item.treeList is).isEmpty = true) := by
            rcases ns with _ | _ <;> rcases is with _ | _ <;> simp_all [Item.treeList]
          simp only [SBody.erase, moduleBody, hne, ite_false, hI']
    rintro ⟨body, ⟨r₇, hr₇⟩⟩ ⟨hB, h⟩
    take_tok h
    simp only [expect_cons, ok_bind]
    exact ⟨_, _, rfl, by simp [SItem.erase, Item.tree, Item.kind, hB], h⟩

/-- `readItems` reads the tokens of items as their trees, before the word
`locs` at the top of a module, or before `}` in a body. -/
theorem Item.readsList (top : Bool) : ∀ is : List (Item d), Item.TypesWritableList is →
    Reads (readItems top) SItem.eraseList (Item.treeList is) (Item.tokensList is) (itemsEnd top)
  | [], _, ts, rest, h, hs => by
    simp only [Item.tokensList, List.nil_append] at h
    match ts, h with
    | [], h =>
      rw [readItems.eq_2 _ _ fun _ _ _ he => by simp at he]
      exact ⟨[], _, rfl, rfl, h⟩
    | ⟨t, p⟩ :: ts', h =>
      have ht : itemsEnd top t := hs t (by simp [← h])
      cases top with
      | true =>
        obtain rfl : t = .word "locs" := ht
        rw [readItems.eq_1]
        exact ⟨[], _, rfl, rfl, h⟩
      | false =>
        obtain rfl : t = .rbrace := ht
        rw [readItems.eq_2 _ _ fun _ _ _ he => by simp at he]
        exact ⟨[], _, rfl, rfl, h⟩
  | i :: is, ht, ts, rest, h, hs => by
    obtain ⟨hi, his⟩ := ht
    have hr := Item.reads i hi
    have hrs := Item.readsList top is his
    simp only [Item.tokensList, List.append_assoc] at h
    rw [Item.tokens_eq i, List.cons_append] at h
    take_pos h p
    obtain ⟨si, ⟨r, hr'⟩, h₁, h₂, h₃⟩ := hr p _ (Item.tokensList is ++ rest) h fun _ _ => trivial
    obtain ⟨sis, ⟨r', hr''⟩, h₄, h₅, h₆⟩ := hrs r rest h₃ hs
    have hk : ¬(top = true ∧ i.kind = "locs") := by cases i <;> simp [Item.kind]
    rw [readItems.eq_1]
    simp only [hk, ↓reduceIte, h₁, ok_bind, h₄]
    exact ⟨_, _, rfl, by simp [SItem.eraseList, Item.treeList, h₂, h₅], h₆⟩
end

/-- The grammar step: on the tokens of a module, then `eof`, at any
positions, `readModule` gives the module's tree, up to positions, when each
type the module writes is written as a type and its location table is
within the limits. -/
theorem readModule_tokens {m : Module d}
    (ht : ∀ i ∈ m.items, i.TypesWritable) (hl : m.locs.InLimits)
    {ts : List Token} (h : ts.map (·.tok) = m.tokens ++ [.eof]) :
    ∃ s, readModule ts = .ok s ∧ s.erase = m.tree := by
  simp only [Module.tokens, List.append_assoc] at h
  have hst : ∀ t ∈ (m.items.flatMap Item.tokens ++ (m.locs.tokens ++ [Tok.eof])).head?,
      t ≠ .comma ∧ t ≠ .word "dialects" := by
    apply head?_append
    · rw [← Item.tokensList_eq_flatMap]
      simpa using head_items m.items [] (fun t => t ≠ .comma ∧ t ≠ .word "dialects") (by simp)
        (by simp)
    · simp [LocTable.tokens]
  rw [← Item.tokensList_eq_flatMap] at h
  obtain ⟨ns, ⟨r₀, hr₀⟩, h₀, h₀', h₀''⟩ := readDialects_reads m.dialects ts _ h
    (by rw [← Item.tokensList_eq_flatMap] at hst; exact hst)
  obtain ⟨items, ⟨r, hr⟩, h₁, h₂, h₃⟩ := Item.readsList true m.items
    ((Item.typesWritableList_iff _).mpr ht) r₀ _ h₀'' (by simp [LocTable.tokens, itemsEnd])
  have h₃' : r.map (·.tok) = .word "locs" :: (m.locs.tokens.tail ++ [.eof]) := by
    simpa [LocTable.tokens] using h₃
  obtain ⟨q, r', rfl, -⟩ := map_tok_cons h₃'
  obtain ⟨locs, ⟨r₂, hr₂⟩, h₄, h₅, h₆⟩ := LocTable.reads m.locs hl _ [.eof] h₃ fun _ _ => trivial
  take_tok h₆
  rw [readModule.eq_1]
  simp only [h₀, ok_bind, h₁, h₄, expect_cons]
  exact ⟨_, rfl, by simp [SModule.erase, Module.tree, ← h₀', ← Item.treeList_eq_map, h₂, ← h₅]⟩

variable [DialectSignature d]

mutual
/-- Each type that a well-formed item writes is written as a type. -/
theorem Item.WellFormed.typesWritable : ∀ {i : Item d}, i.WellFormed → i.TypesWritable
  | .func _, h => fun t ht => (Func.WellFormed.types h t ht).1
  | .module _ _ _, h => Item.WellFormed.typesWritableList h.2

/-- Each type that well-formed items write is written as a type. -/
theorem Item.WellFormed.typesWritableList : ∀ {is : List (Item d)}, Item.WellFormedList is →
    Item.TypesWritableList is
  | [], _ => trivial
  | _ :: _, h => ⟨Item.WellFormed.typesWritable h.1, Item.WellFormed.typesWritableList h.2⟩
end

/-- The grammar step for a well-formed module: each type it writes is
written as a type, and its location table is within the limits. -/
theorem Module.WellFormed.readModule_tokens {m : Module d} (h : m.WellFormed) {ts : List Token}
    (hts : ts.map (·.tok) = m.tokens ++ [.eof]) :
    ∃ s, readModule ts = .ok s ∧ s.erase = m.tree :=
  Fir.readModule_tokens (fun i hi => (h.items i hi).typesWritable) h.locs hts

/-- The first two steps of the parser read the printed text of a
well-formed module as the module's tree, up to positions. -/
theorem Module.WellFormed.read_print {m : Module d} (h : m.WellFormed) :
    ∃ ts s, lex m.print = .ok ts ∧ readModule ts = .ok s ∧ s.erase = m.tree := by
  obtain ⟨ts, h₁, h₂⟩ := h.lex_print
  obtain ⟨s, h₃, h₄⟩ := h.readModule_tokens h₂
  exact ⟨ts, s, h₁, h₃, h₄⟩

/-- The first two steps of the parser read the printed text of a valid
module of a dialect with lawful text as the module's tree. -/
theorem Module.Valid.read_print [DialectValidation d] [LawfulDialectText d] {m : Module d}
    (h : m.Valid) : ∃ ts s, lex m.print = .ok ts ∧ readModule ts = .ok s ∧ s.erase = m.tree :=
  (validIsWellFormed m h).read_print

end Fir
