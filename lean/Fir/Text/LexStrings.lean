import Fir.Text.LexTokens

/-!
# Reading printed strings and symbols

`quote` writes each character of a string in its one spelling, with
`escapeChar`, and the lexer reads each spelling back as the character: `\"`,
`\\`, `\n` and `\t` as themselves, `\u{h}` as the escaped character whose
code point `h` writes, and every other character as itself
(`lexStringFrom_escapeChar`). So a quoted string reads back as the string,
whatever it holds (`lexStringFrom_quote`). A symbol is written bare when its
name is a word, and quoted otherwise, which is when the lexer accepts it
quoted.

With these, every token that can be written spells itself (`Tok.spells`).
-/

namespace Fir.Text

/-- `\u{h}`, with the digits that `hex` writes, reads back as the escaped
character whose code point they write. -/
theorem unicodeEscape_toDigits {c : Char} (h₁ : isEscaped c = true) (h₂ : c ≠ '\n') (h₃ : c ≠ '\t')
    (p : TextPos) : unicodeEscape (Nat.toDigits 16 c.toNat) p = .ok c := by
  have hc : ∀ h, Char.ofNatAux c.toNat h = c := fun _ => Char.ext (UInt32.toNat_inj.mp (by simp; rfl))
  have hz : ¬ ((Nat.toDigits 16 c.toNat).length > 1 ∧ (Nat.toDigits 16 c.toNat).head? = some '0') := by
    rintro ⟨hl, hh⟩
    rcases Nat.eq_zero_or_pos c.toNat with h0 | h0
    · rw [h0, Nat.toDigits_zero] at hl; simp at hl
    · exact head_toDigits_ne_zero (by decide) (by decide) h0 hh
  unfold unicodeEscape
  simp only [hexValue_toDigits, List.isEmpty_iff, Nat.toDigits_ne_nil, ite_false]
  have hv : c.toNat.isValidChar := c.valid
  simp only [hv, not_true_eq_false, ↓reduceDIte, hc, h₂, h₃, h₁, ite_false, ite_true,
    Bool.and_eq_true, decide_eq_true_eq, hz]

theorem escapeChar_quote : (escapeChar '"').toList = ['\\', '"'] := by decide
theorem escapeChar_backslash : (escapeChar '\\').toList = ['\\', '\\'] := by decide
theorem escapeChar_lf : (escapeChar '\n').toList = ['\\', 'n'] := by decide
theorem escapeChar_tab : (escapeChar '\t').toList = ['\\', 't'] := by decide

/-- How `escapeChar` writes a character that is escaped as `\u{h}`. -/
theorem escapeChar_unicode {c : Char} (e₁ : c ≠ '"') (e₂ : c ≠ '\\') (e₃ : c ≠ '\n') (e₄ : c ≠ '\t')
    (e₅ : isEscaped c = true) :
    (escapeChar c).toList = '\\' :: 'u' :: '{' :: (Nat.toDigits 16 c.toNat ++ ['}']) := by
  simp only [escapeChar, e₁, e₂, e₃, e₄, e₅, ite_true, ite_false, hex, String.toList_append,
    String.toList_ofList]
  rfl

/-- How `escapeChar` writes a character that is not escaped: as itself. -/
theorem escapeChar_self {c : Char} (e₁ : c ≠ '"') (e₂ : c ≠ '\\') (e₃ : c ≠ '\n') (e₄ : c ≠ '\t')
    (e₅ : isEscaped c = false) : (escapeChar c).toList = [c] := by
  simp [escapeChar, e₁, e₂, e₃, e₄, e₅]

/-- The spelling of one character of a string reads back as the character. -/
theorem lexStringFrom_escapeChar (c : Char) {l rest cs₀ : List Char}
    (hl : l = (escapeChar c).toList ++ rest) (h : l.length ≤ cs₀.length) (p start : TextPos)
    (acc : List Char) :
    ∃ q h', lexStringFrom cs₀ l h p start acc = lexStringFrom cs₀ rest h' q start (c :: acc) := by
  by_cases e₁ : c = '"'
  · subst e₁
    rw [escapeChar_quote, List.cons_append, List.cons_append, List.nil_append] at hl
    subst hl
    rw [lexStringFrom.eq_3]
    simp only [lexEscape, ok_bind]
    exact ⟨_, by simp at h ⊢; omega, rfl⟩
  by_cases e₂ : c = '\\'
  · subst e₂
    rw [escapeChar_backslash, List.cons_append, List.cons_append, List.nil_append] at hl
    subst hl
    rw [lexStringFrom.eq_3]
    simp only [lexEscape, ok_bind]
    exact ⟨_, by simp at h ⊢; omega, rfl⟩
  by_cases e₃ : c = '\n'
  · subst e₃
    rw [escapeChar_lf, List.cons_append, List.cons_append, List.nil_append] at hl
    subst hl
    rw [lexStringFrom.eq_3]
    simp only [lexEscape, ok_bind]
    exact ⟨_, by simp at h ⊢; omega, rfl⟩
  by_cases e₄ : c = '\t'
  · subst e₄
    rw [escapeChar_tab, List.cons_append, List.cons_append, List.nil_append] at hl
    subst hl
    rw [lexStringFrom.eq_3]
    simp only [lexEscape, ok_bind]
    exact ⟨_, by simp at h ⊢; omega, rfl⟩
  by_cases e₅ : isEscaped c = true
  · rw [escapeChar_unicode e₁ e₂ e₃ e₄ e₅] at hl
    simp only [List.cons_append, List.append_assoc, List.nil_append] at hl
    subst hl
    have hd : ∀ x ∈ Nat.toDigits 16 c.toNat, isHexDigit x = true := fun _ hx =>
      isHexDigit_of_mem_toDigits hx
    have ht :
        (Nat.toDigits 16 c.toNat ++ '}' :: rest).takeWhile isHexDigit = Nat.toDigits 16 c.toNat := by
      rw [List.takeWhile_append_of_pos hd]; simp [isHexDigit]
    have hdw : (Nat.toDigits 16 c.toNat ++ '}' :: rest).dropWhile isHexDigit = '}' :: rest := by
      rw [List.dropWhile_append_of_pos hd]; simp [isHexDigit]
    rw [lexStringFrom.eq_3, lexEscape.eq_5]
    split
    · rename_i after heq
      rw [hdw] at heq
      cases heq
      simp only [ht, unicodeEscape_toDigits e₅ e₃ e₄, Except.map, ok_bind]
      exact ⟨_, by simp at h ⊢; omega, rfl⟩
    · rename_i hne
      exact absurd hdw (hne rest)
  · rw [escapeChar_self e₁ e₂ e₃ e₄ (by simpa using e₅), List.cons_append, List.nil_append] at hl
    subst hl
    rw [lexStringFrom.eq_4 _ _ _ _ _ _ _ e₁ e₂]
    simp only [e₅, Bool.false_eq_true, ite_false]
    exact ⟨_, by simp at h ⊢; omega, rfl⟩

/-- The spellings of the characters of a string, then the closing quote,
read back as the string. -/
theorem lexStringFrom_quote (s : List Char) {l cs cs₀ : List Char}
    (hl : l = s.flatMap (escapeChar · |>.toList) ++ '"' :: cs) (h : l.length ≤ cs₀.length)
    (p start : TextPos) (acc : List Char) :
    ∃ q h', lexStringFrom cs₀ l h p start acc =
      .ok (String.ofList (acc.reverse ++ s), ⟨cs, h'⟩, q) := by
  induction s generalizing l p acc with
  | nil =>
    simp only [List.flatMap_nil, List.nil_append] at hl
    subst hl
    rw [lexStringFrom.eq_2]
    exact ⟨p.advance 1, by simp at h; omega, by simp⟩
  | cons c s ih =>
    simp only [List.flatMap_cons, List.append_assoc] at hl
    obtain ⟨q, h', e⟩ := lexStringFrom_escapeChar c hl h p start acc
    obtain ⟨q', h'', e'⟩ := ih rfl h' q (c :: acc)
    exact ⟨q', h'', by rw [e, e']; simp⟩

/-- The characters of a quoted string. -/
theorem toList_quote (s : String) :
    (quote s).toList = '"' :: (s.toList.flatMap (escapeChar · |>.toList) ++ ['"']) := by
  simp [quote, List.flatMap_map]

/-- A string reads back as itself, up to its closing quote. -/
theorem lexString_quote (s : String) (cs : List Char) (p start : TextPos) :
    ∃ q h, lexString (s.toList.flatMap (escapeChar · |>.toList) ++ '"' :: cs) p start =
      .ok (s, ⟨cs, h⟩, q) := by
  obtain ⟨q, h, e⟩ := lexStringFrom_quote s.toList rfl (Nat.le_refl _) p start []
  exact ⟨q, h, by rw [lexString, e]; simp [String.ofList_toList]⟩

/-- A string token. -/
theorem readsToken_str (s : String) (cs : List Char) :
    ReadsToken '"' (s.toList.flatMap (escapeChar · |>.toList) ++ '"' :: cs) cs (.str s) := by
  intro p
  obtain ⟨q, h, e⟩ := lexString_quote s cs (p.advance 1) p
  unfold lexToken
  simp (config := { decide := true }) only [ite_true, ite_false]
  rw [e]
  exact ⟨_, by simp; omega, rfl⟩

/-- A symbol whose name is not a word: `@`, then its name quoted. -/
theorem readsToken_quotedSym {s : String} (hs : isWord s = false) (cs : List Char) :
    ReadsToken '@' ('"' :: (s.toList.flatMap (escapeChar · |>.toList) ++ '"' :: cs)) cs (.sym s) := by
  intro p
  obtain ⟨q, h, e⟩ := lexString_quote s cs (p.advance 2) (p.advance 1)
  unfold lexToken
  simp (config := { decide := true }) only [ite_true, ite_false]
  rw [lexAt]
  simp (config := { decide := true }) only [ite_true, ite_false]
  rw [e]
  simp only [ok_bind, hs, Bool.false_eq_true, ite_false]
  exact ⟨_, by simp; omega, rfl⟩

/-- A symbol whose name is a word: `@`, then its name. -/
theorem readsToken_wordSym {c : Char} {cs₀ cs : List Char} (hc : isWordStart c = true)
    (h₀ : ∀ x ∈ cs₀, isNameChar x = true) (hs : Boundary cs) :
    ReadsToken '@' (c :: (cs₀ ++ cs)) cs (.sym (String.ofList (c :: cs₀))) := by
  intro p
  obtain ⟨h₁, h₂⟩ := takeWhile_name h₀ hs
  unfold lexToken
  simp (config := { decide := true }) only [ite_true, ite_false]
  rw [lexAt]
  simp only [isDigit_of_isWordStart hc, hc, Bool.false_eq_true, ite_false, ite_true, h₁, h₂]
  exact ⟨_, by simp; omega, rfl⟩

/-! # Every token -/

/-- A word: a character that starts a word, then name characters. -/
theorem isWord_iff {s : String} : isWord s = true ↔
    ∃ c cs, s.toList = c :: cs ∧ isWordStart c = true ∧ ∀ x ∈ cs, isNameChar x = true := by
  unfold isWord
  split
  · rename_i c cs h
    simp only [h, Bool.and_eq_true, List.all_eq_true, List.cons.injEq]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨c, cs, ⟨rfl, rfl⟩, h₁, h₂⟩
    · rintro ⟨_, _, ⟨rfl, rfl⟩, h₁, h₂⟩
      exact ⟨h₁, h₂⟩
  · rename_i h
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro c cs hc
    rw [h] at hc
    cases hc

/-- A token that `lexToken` reads, starting with a character that is not
whitespace or `/`, spells itself. -/
theorem spells_of_reads {c : Char} {s : List Char} {t : Tok}
    (hc : c ≠ ' ' ∧ c ≠ '\t' ∧ c ≠ '\n' ∧ c ≠ '/')
    (hr : ∀ cs, Boundary cs → ReadsToken c (s ++ cs) cs t) :
    Spells (c :: s) [t] :=
  fun cs us hs h => by simpa using Lexes.token hc (hr cs hs) h

/-- A natural number's digits, as an integer token. -/
theorem spells_nat (n : Nat) : Spells (Nat.toDigits 10 n) [.int n] := by
  obtain ⟨d, ds, he⟩ := toDigits_cons n
  have hn := isNameChar_of_isDigit (isDigit_of_toDigits (he ▸ List.mem_cons_self ..))
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h₁, h₂, h₃, h₄⟩ := ne_of_isNameChar hn
  rw [he]
  exact spells_of_reads ⟨h₁, h₂, h₃, h₄⟩ fun cs hs => readsToken_nat he hs

/-- Every token that can be written spells itself. -/
theorem Tok.spells {t : Tok} (ht : t.Writable) : Spells t.spell.toList [t] := by
  cases t with
  | value n =>
    rw [show (Tok.value n).spell.toList = '%' :: n.toList by simp [Tok.spell]]
    exact spells_of_reads (by decide) fun cs hs => by simpa using readsToken_name (.inl rfl) ht hs
  | label n =>
    rw [show (Tok.label n).spell.toList = '^' :: n.toList by simp [Tok.spell]]
    exact spells_of_reads (by decide) fun cs hs => by simpa using readsToken_name (.inr rfl) ht hs
  | sym s =>
    by_cases hw : isWord s = true
    · obtain ⟨c, cs₀, he, hc, h₀⟩ := isWord_iff.mp hw
      rw [show (Tok.sym s).spell.toList = '@' :: c :: cs₀ by
        simp [Tok.spell, printSymbol, hw, he]]
      refine spells_of_reads (by decide) fun cs hs => ?_
      have := readsToken_wordSym hc h₀ hs
      rwa [← he, String.ofList_toList] at this
    · rw [show (Tok.sym s).spell.toList =
          '@' :: '"' :: (s.toList.flatMap (escapeChar · |>.toList) ++ ['"']) by
        simp [Tok.spell, printSymbol, hw, toList_quote]]
      exact spells_of_reads (by decide) fun cs _ => by
        simpa using readsToken_quotedSym (by simpa using hw) cs
  | locRef r =>
    obtain ⟨d, ds, he⟩ := toDigits_cons r
    rw [show (Tok.locRef r).spell.toList = '@' :: d :: ds by
      simp [Tok.spell, printLocRef, he]]
    exact spells_of_reads (by decide) fun cs hs => readsToken_locRef ht he hs
  | word w =>
    obtain ⟨c, cs₀, he, hc, h₀⟩ := isWord_iff.mp ht
    have hn : isNameChar c = true := by simp [isNameChar, hc]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h₁, h₂, h₃, h₄⟩ := ne_of_isNameChar hn
    rw [show (Tok.word w).spell.toList = c :: cs₀ by simp [Tok.spell, he]]
    refine spells_of_reads ⟨h₁, h₂, h₃, h₄⟩ fun cs hs => ?_
    have := readsToken_word hc h₀ hs
    rwa [← he, String.ofList_toList] at this
  | int i =>
    cases i with
    | ofNat n =>
      rw [show (Tok.int (.ofNat n)).spell.toList = Nat.toDigits 10 n by
        simp only [Tok.spell, printInt]; exact Nat.toList_repr]
      exact spells_nat n
    | negSucc m =>
      obtain ⟨d, ds, he⟩ := toDigits_cons (m + 1)
      rw [show (Tok.int (.negSucc m)).spell.toList = '-' :: d :: ds by
        simp only [Tok.spell, printInt, ← he]
        exact (String.toList_append (s := "-") (t := Nat.repr (m + 1))).trans (by simp)]
      exact spells_of_reads (by decide) fun cs hs => readsToken_neg he hs
  | str s =>
    rw [show (Tok.str s).spell.toList = '"' :: (s.toList.flatMap (escapeChar · |>.toList) ++ ['"']) by
      simp [Tok.spell, toList_quote]]
    exact spells_of_reads (by decide) fun cs _ => by simpa using readsToken_str s cs
  | eof => exact ht.elim
  | _ => exact fun _ _ _ h => Tok.lexes_punct (by exact trivial) h

end Fir.Text
