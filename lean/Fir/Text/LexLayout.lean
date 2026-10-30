import Fir.Text.LexStrings

/-!
# Reading the printer's layout

The printer puts tokens side by side, or separates them with spaces, line
feeds and indentation. This section gives the lemmas that read such a text
one piece at a time, from its first character: whitespace is dropped
(`Lexes.space`, `Lexes.lf`, `Lexes.spaces`), each token is read by
`Tok.spells`, and lists written with `", "` or `" "` between their elements
are read element by element (`spells_commaSep`, `spells_spaceSep`).

Text that ends with punctuation or a line feed is read before any
characters at all, not only before the end of a token (`SpellsAny`). Every
line, block, region, item and module ends with one, so they are read before
whatever follows them.
-/

namespace Fir.Text

/-- The characters `s` spell the tokens `ts` before any characters: `s`
ends with punctuation or whitespace. -/
def SpellsAny (s : List Char) (ts : List Tok) : Prop :=
  ∀ cs us, Lexes cs us → Lexes (s ++ cs) (ts ++ us)

theorem Spells.nil : Spells [] [] := fun _ _ _ h => h

/-- Text that keeps a boundary: before characters at the end of a token, it
is at the end of a token too. It is empty, or it starts with a character that
is not a name character. -/
def StartsBoundary (s : List Char) : Prop := ∀ cs, Boundary cs → Boundary (s ++ cs)

theorem startsBoundary_cons {c : Char} {s : List Char} (h : isNameChar c = false) :
    StartsBoundary (c :: s) := fun _ _ => boundary_cons h

/-- Two texts side by side, the second starting at the end of a token. -/
theorem Spells.append {a b : List Char} {ta tb : List Tok} (h₁ : Spells a ta) (h₂ : Spells b tb)
    (hb : StartsBoundary b) : Spells (a ++ b) (ta ++ tb) := fun cs us hs h => by
  simpa [List.append_assoc] using h₁ _ _ (hb cs hs) (h₂ cs us hs h)

/-- Text after text that ends with punctuation or whitespace. -/
theorem SpellsAny.append_any {a b : List Char} {ta tb : List Tok} (h₁ : SpellsAny a ta)
    (h₂ : SpellsAny b tb) : SpellsAny (a ++ b) (ta ++ tb) := fun cs us h => by
  simpa [List.append_assoc] using h₁ _ _ (h₂ cs us h)

/-- Text that ends with punctuation or whitespace, after text that is read
at the end of a token. -/
theorem Spells.append_any {a b : List Char} {ta tb : List Tok} (h₁ : Spells a ta)
    (h₂ : SpellsAny b tb) (hb : ∀ cs, Boundary (b ++ cs)) : SpellsAny (a ++ b) (ta ++ tb) := fun cs us h => by
  simpa [List.append_assoc] using h₁ _ _ (hb cs) (h₂ cs us h)

/-! # Whitespace and punctuation -/

theorem Spells.space {s : List Char} {ts : List Tok} (h : Spells s ts) : Spells (' ' :: s) ts :=
  fun cs us hs hl => (h cs us hs hl).space

theorem SpellsAny.space {s : List Char} {ts : List Tok} (h : SpellsAny s ts) :
    SpellsAny (' ' :: s) ts :=
  fun cs us hl => (h cs us hl).space

theorem SpellsAny.lf {s : List Char} {ts : List Tok} (h : SpellsAny s ts) : SpellsAny ('\n' :: s) ts :=
  fun cs us hl => (h cs us hl).lf

theorem SpellsAny.nil : SpellsAny [] [] := fun _ _ h => h

/-- Indentation is dropped. -/
theorem toList_indent (n : Nat) : (indent n).toList = List.replicate n ' ' := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [indent, String.pushn_eq_repeat_push, Nat.repeat, ← String.pushn_eq_repeat_push,
      String.toList_push]
    rw [indent] at ih
    rw [ih, List.replicate_succ']

theorem SpellsAny.indent {s : List Char} {ts : List Tok} (h : SpellsAny s ts) (n : Nat) :
    SpellsAny ((Fir.indent n).toList ++ s) ts := fun cs us hl => by
  rw [toList_indent, List.append_assoc]
  exact (h cs us hl).spaces n

/-- Punctuation, before text that is read at the end of a token. -/
theorem Spells.punct {t : Tok} (ht : t.IsPunct) {c : Char} {cs₀ s : List Char} {ts : List Tok}
    (he : t.spell.toList = c :: cs₀) (h : Spells s ts) : Spells (c :: (cs₀ ++ s)) (t :: ts) :=
  fun cs us hs hl => by
    have := Tok.lexes_punct ht (h cs us hs hl)
    rw [he] at this
    simpa using this

/-- Punctuation, before text that is read before any text. -/
theorem SpellsAny.punct_any {t : Tok} (ht : t.IsPunct) {c : Char} {cs₀ s : List Char} {ts : List Tok}
    (he : t.spell.toList = c :: cs₀) (h : SpellsAny s ts) : SpellsAny (c :: (cs₀ ++ s)) (t :: ts) :=
  fun cs us hl => by
    have := Tok.lexes_punct ht (h cs us hl)
    rw [he] at this
    simpa using this

theorem Spells.comma {s ts} (h : Spells s ts) : Spells (',' :: s) (.comma :: ts) :=
  Spells.punct (t := .comma) (cs₀ := []) trivial (by decide) h
theorem SpellsAny.lbrace {s ts} (h : SpellsAny s ts) : SpellsAny ('{' :: s) (.lbrace :: ts) :=
  SpellsAny.punct_any (t := .lbrace) (cs₀ := []) trivial (by decide) h
theorem SpellsAny.rbrace {s ts} (h : SpellsAny s ts) : SpellsAny ('}' :: s) (.rbrace :: ts) :=
  SpellsAny.punct_any (t := .rbrace) (cs₀ := []) trivial (by decide) h
theorem SpellsAny.rparen {s ts} (h : SpellsAny s ts) : SpellsAny (')' :: s) (.rparen :: ts) :=
  SpellsAny.punct_any (t := .rparen) (cs₀ := []) trivial (by decide) h
theorem SpellsAny.colon {s ts} (h : SpellsAny s ts) : SpellsAny (':' :: s) (.colon :: ts) :=
  SpellsAny.punct_any (t := .colon) (cs₀ := []) trivial (by decide) h
theorem SpellsAny.lparen {s ts} (h : SpellsAny s ts) : SpellsAny ('(' :: s) (.lparen :: ts) :=
  SpellsAny.punct_any (t := .lparen) (cs₀ := []) trivial (by decide) h
theorem SpellsAny.eq {s ts} (h : SpellsAny s ts) : SpellsAny ('=' :: s) (.eq :: ts) :=
  SpellsAny.punct_any (t := .eq) (cs₀ := []) trivial (by decide) h

/-! # Tokens -/

theorem Spells.tok_any {t : Tok} (ht : t.Writable) {s : List Char} {ts : List Tok} (h : SpellsAny s ts)
    (hs : ∀ cs, Boundary (s ++ cs)) : SpellsAny (t.spell.toList ++ s) (t :: ts) :=
  Spells.append_any (Tok.spells ht) h hs

/-- A word written in the printer's text. -/
theorem spells_word {w : String} (hw : isWord w = true) : Spells w.toList [.word w] :=
  Tok.spells (t := .word w) hw

/-! # Reading from the first character

The printer's text is read piece by piece from its first character. Each
lemma below reads one piece before characters `cs` that lex to `us`. -/

theorem Lexes.punct {t : Tok} (ht : t.IsPunct) {pre cs : List Char} {us : List Tok}
    (he : t.spell.toList = pre) (h : Lexes cs us) : Lexes (pre ++ cs) (t :: us) :=
  he ▸ Tok.lexes_punct ht h

theorem Lexes.lparen {cs us} (h : Lexes cs us) : Lexes ('(' :: cs) (.lparen :: us) :=
  Lexes.punct (pre := ['(']) (t := .lparen) trivial (by decide) h
theorem Lexes.rparen {cs us} (h : Lexes cs us) : Lexes (')' :: cs) (.rparen :: us) :=
  Lexes.punct (pre := [')']) (t := .rparen) trivial (by decide) h
theorem Lexes.lbrace {cs us} (h : Lexes cs us) : Lexes ('{' :: cs) (.lbrace :: us) :=
  Lexes.punct (pre := ['{']) (t := .lbrace) trivial (by decide) h
theorem Lexes.rbrace {cs us} (h : Lexes cs us) : Lexes ('}' :: cs) (.rbrace :: us) :=
  Lexes.punct (pre := ['}']) (t := .rbrace) trivial (by decide) h
theorem Lexes.colon {cs us} (h : Lexes cs us) : Lexes (':' :: cs) (.colon :: us) :=
  Lexes.punct (pre := [':']) (t := .colon) trivial (by decide) h
theorem Lexes.eq {cs us} (h : Lexes cs us) : Lexes ('=' :: cs) (.eq :: us) :=
  Lexes.punct (pre := ['=']) (t := .eq) trivial (by decide) h
theorem Lexes.arrow {cs us} (h : Lexes cs us) : Lexes ('-' :: '>' :: cs) (.arrow :: us) :=
  Lexes.punct (pre := ['-', '>']) (t := .arrow) trivial (by decide) h

/-- A token whose spelling is `pre`, at the end of a token. -/
theorem Lexes.tok {t : Tok} (ht : t.Writable) {pre cs : List Char} {us : List Tok}
    (he : t.spell.toList = pre) (hb : Boundary cs) (h : Lexes cs us) : Lexes (pre ++ cs) (t :: us) :=
  he ▸ Tok.spells ht cs us hb h

theorem Lexes.word {w : String} (hw : isWord w = true) {cs us} (hb : Boundary cs) (h : Lexes cs us) :
    Lexes (w.toList ++ cs) (.word w :: us) :=
  Lexes.tok (t := .word w) hw rfl hb h

theorem Lexes.value {n : String} (hn : isName n = true) {cs us} (hb : Boundary cs) (h : Lexes cs us) :
    Lexes ('%' :: (n.toList ++ cs)) (.value n :: us) :=
  Lexes.tok (t := .value n) (pre := '%' :: n.toList) hn (by simp [Tok.spell]) hb h

theorem Lexes.label {n : String} (hn : isName n = true) {cs us} (hb : Boundary cs) (h : Lexes cs us) :
    Lexes ('^' :: (n.toList ++ cs)) (.label n :: us) :=
  Lexes.tok (t := .label n) (pre := '^' :: n.toList) hn (by simp [Tok.spell]) hb h

theorem Lexes.sym (s : String) {cs us} (hb : Boundary cs) (h : Lexes cs us) :
    Lexes ((printSymbol s).toList ++ cs) (.sym s :: us) :=
  Lexes.tok (t := .sym s) trivial rfl hb h

theorem Lexes.locRef {r : Nat} (hr : r < Location.limit) {cs us} (hb : Boundary cs) (h : Lexes cs us) :
    Lexes ((printLocRef r).toList ++ cs) (.locRef r :: us) :=
  Lexes.tok (t := .locRef r) hr rfl hb h

/-- A line or a column, which a location writes with `toString`. -/
theorem Lexes.nat (n : Nat) {cs us} (hb : Boundary cs) (h : Lexes cs us) :
    Lexes ((toString n).toList ++ cs) (.int n :: us) :=
  Lexes.tok (t := .int n) trivial rfl hb h

theorem Lexes.quote (s : String) {cs us} (hb : Boundary cs) (h : Lexes cs us) :
    Lexes ((quote s).toList ++ cs) (.str s :: us) :=
  Lexes.tok (t := .str s) trivial rfl hb h

/-- A word that the printer writes as a literal, such as `func`. -/
theorem Lexes.lit (w : String) (pre : List Char) {cs us} (hb : Boundary cs) (h : Lexes cs us)
    (hw : isWord w = true := by decide) (he : w.toList = pre := by decide) :
    Lexes (pre ++ cs) (.word w :: us) :=
  Lexes.tok (t := .word w) hw he hb h

theorem boundary_space (cs : List Char) : Boundary (' ' :: cs) := boundary_cons (by decide)

/-! # Lists -/

/-- Each string of a list spells the matching list of tokens. -/
def SpellsEach : List String → List (List Tok) → Prop
  | [], [] => True
  | s :: ss, ts :: tss => Spells s.toList ts ∧ SpellsEach ss tss
  | _, _ => False

theorem SpellsEach.map {α : Type} {xs : List α} {f : α → String} {g : α → List Tok}
    (h : ∀ x ∈ xs, Spells (f x).toList (g x)) : SpellsEach (xs.map f) (xs.map g) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨h x (.head _), ih fun y hy => h y (.tail _ hy)⟩

theorem SpellsEach.append {a c : List String} {b d : List (List Tok)} (h₁ : SpellsEach a b)
    (h₂ : SpellsEach c d) : SpellsEach (a ++ c) (b ++ d) := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [SpellsEach]
  | cons s ss ih =>
    cases b with
    | nil => exact h₁.elim
    | cons ts tss => exact ⟨h₁.1, ih h₁.2⟩

/-- A list written with `", "` between its elements. -/
theorem spells_commaSep : ∀ {ss : List String} {tss : List (List Tok)}, SpellsEach ss tss →
    Spells (", ".intercalate ss).toList ([Tok.comma].intercalate tss)
  | [], [], _ => by simpa using Spells.nil
  | [s], [ts], h => by simpa using h.1
  | s :: s' :: ss, ts :: ts' :: tss, h => by
    rw [String.intercalate_cons_cons, List.intercalate_cons_cons, String.toList_append,
      String.toList_append, List.append_assoc, List.append_assoc]
    refine Spells.append h.1 ?_ (startsBoundary_cons (by decide))
    exact Spells.comma (Spells.space (spells_commaSep (ss := s' :: ss) h.2))
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | [_], _ :: _ :: _, h => h.2.elim
  | _ :: _ :: _, [_], h => h.2.elim

/-- A list written with `" "` between its elements. -/
theorem spells_spaceSep : ∀ {ss : List String} {tss : List (List Tok)}, SpellsEach ss tss →
    Spells (" ".intercalate ss).toList tss.flatten
  | [], [], _ => by simpa using Spells.nil
  | [s], [ts], h => by simpa using h.1
  | s :: s' :: ss, ts :: ts' :: tss, h => by
    rw [String.intercalate_cons_cons, List.flatten_cons, String.toList_append, String.toList_append,
      List.append_assoc]
    refine Spells.append h.1 ?_ (startsBoundary_cons (by decide))
    exact Spells.space (spells_spaceSep (ss := s' :: ss) h.2)
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | [_], _ :: _ :: _, h => h.2.elim
  | _ :: _ :: _, [_], h => h.2.elim

/-- Every token of an element of a list written with separators is a token
of the list. -/
theorem forall_mem_intercalate {P : Tok → Prop} {sep : List Tok} :
    ∀ {tss : List (List Tok)}, (∀ t ∈ sep.intercalate tss, P t) → ∀ ts ∈ tss, ∀ t ∈ ts, P t
  | [], _ => by simp
  | [ts], h => by simpa using h
  | ts :: ts' :: tss, h => by
    rw [List.intercalate_cons_cons, List.forall_mem_append, List.forall_mem_append] at h
    intro us hus
    rcases List.mem_cons.mp hus with rfl | hus
    · exact h.1.1
    · exact forall_mem_intercalate h.2 us hus

end Fir.Text
