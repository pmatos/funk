import Fir.Text.LexNumbers

/-!
# Reading one printed token

The lexer reads a printed token back as itself, whatever follows it, as long
as what follows does not start with a name character. That is maximal munch
seen from the printer's side: a value, a label, a symbol written as a word,
a location reference, a word or an integer ends at the first character that
is not a name character, so the printer never writes one directly before a
name character. Punctuation ends where it is, so it may be followed by
anything, and the printer writes `(` and `:` directly before a word or a
number, as in `h(i32)` and `"f":2:3`.

Three predicates on characters say this:

* `Boundary cs`: `cs` is empty or does not start with a name character;
* `Lexes cs ts`: `cs` lexes to `ts`, then `eof`, from any position and after
  any tokens already read;
* `Spells s ts`: `s`, followed by any `cs` with `Boundary cs`, lexes to
  `ts`, then the tokens of `cs`.

`Tok.spells` proves `Spells` for the spelling of every token that can be
written. This section covers the tokens that hold no string: punctuation,
names, words, numbers and location references. The next covers strings and
symbols.
-/

namespace Fir.Text

/-- `cs` is at the end of a token: it is empty, or it starts with a character
that is not a name character, so no name, word or number runs into it. -/
def Boundary (cs : List Char) : Prop := ∀ c ∈ cs.head?, isNameChar c = false

/-- The characters `cs` lex to the tokens `ts`, then `eof`, from any position
and after any tokens already read. -/
def Lexes (cs : List Char) (ts : List Tok) : Prop :=
  ∀ p acc, ∃ r : List Token, lexFrom cs p acc = .ok (acc.reverse ++ r) ∧ r.map (·.tok) = ts ++ [.eof]

/-- The characters `s` spell the tokens `ts`: followed by characters that
lex and are at the end of a token, they lex to `ts`, then the tokens of
those characters. -/
def Spells (s : List Char) (ts : List Tok) : Prop :=
  ∀ cs us, Boundary cs → Lexes cs us → Lexes (s ++ cs) (ts ++ us)

/-- Binding a result that is there runs what follows on it. -/
theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f : Except ε β) = f a := rfl

theorem boundary_cons {c : Char} {cs : List Char} (h : isNameChar c = false) :
    Boundary (c :: cs) := by
  simpa [Boundary] using h

/-- The empty text lexes to `eof` alone. -/
theorem Lexes.nil : Lexes [] [] := fun p acc => ⟨[⟨.eof, p⟩], by rw [lexFrom]; simp, rfl⟩

/-- A space is dropped. -/
theorem Lexes.space {cs : List Char} {ts : List Tok} (h : Lexes cs ts) : Lexes (' ' :: cs) ts :=
  fun p acc => by rw [lexFrom]; exact h _ _

/-- A line feed is dropped. -/
theorem Lexes.lf {cs : List Char} {ts : List Tok} (h : Lexes cs ts) : Lexes ('\n' :: cs) ts :=
  fun p acc => by rw [lexFrom]; exact h _ _

/-- Spaces are dropped. -/
theorem Lexes.spaces {cs : List Char} {ts : List Tok} (h : Lexes cs ts) (n : Nat) :
    Lexes (List.replicate n ' ' ++ cs) ts := by
  induction n with
  | zero => exact h
  | succ n ih => exact List.replicate_succ .. ▸ ih.space

/-- `lexToken` reads the token `t` from `c :: rest` at every position,
leaving `r`. -/
def ReadsToken (c : Char) (rest r : List Char) (t : Tok) : Prop :=
  ∀ p, ∃ q hr, lexToken c rest p = .ok (t, ⟨r, hr⟩, q)

/-- A token that starts with a character other than whitespace and `/` is
read by `lexToken`. -/
theorem Lexes.token {c : Char} {rest r : List Char} {t : Tok} {us : List Tok}
    (hc : c ≠ ' ' ∧ c ≠ '\t' ∧ c ≠ '\n' ∧ c ≠ '/') (hl : ReadsToken c rest r t) (h : Lexes r us) :
    Lexes (c :: rest) (t :: us) := by
  intro p acc
  obtain ⟨q, hr, hl⟩ := hl p
  obtain ⟨r', h₁, h₂⟩ := h q (⟨t, p⟩ :: acc)
  refine ⟨⟨t, p⟩ :: r', ?_, by simp [h₂]⟩
  rw [lexFrom.eq_6 _ _ _ _ hc.1 hc.2.1 hc.2.2.1 (fun _ h _ => hc.2.2.2 h), hl, ok_bind]
  simp [h₁]

/-! # Punctuation -/

/-- A punctuation token: it ends where it is. -/
def Tok.IsPunct : Tok → Prop
  | .lparen | .rparen | .lbrace | .rbrace | .comma | .colon | .eq | .arrow => True
  | _ => False

/-- Punctuation is read before any characters at all. -/
theorem Tok.lexes_punct {t : Tok} (ht : t.IsPunct) {cs : List Char} {us : List Tok}
    (h : Lexes cs us) : Lexes (t.spell.toList ++ cs) (t :: us) := by
  cases t <;> simp only [Tok.IsPunct] at ht
  all_goals
    simp only [Tok.spell]
    refine Lexes.token (by decide) (fun p => ?_) h
    unfold lexToken
    simp (config := { decide := true }) only [ite_true, ite_false]
    exact ⟨_, by simp, rfl⟩

/-! # Names and words -/

/-- Name characters are read up to the first other character. -/
theorem takeWhile_name {l cs : List Char} (hl : ∀ c ∈ l, isNameChar c = true) (hs : Boundary cs) :
    (l ++ cs).takeWhile isNameChar = l ∧ (l ++ cs).dropWhile isNameChar = cs := by
  rw [List.takeWhile_append_of_pos hl, List.dropWhile_append_of_pos hl]
  match cs, hs with
  | [], _ => simp
  | c :: _, hs => simp [hs c rfl]

/-- The characters of a name are name characters, and there is one. -/
theorem isName_iff {n : String} :
    isName n = true ↔ n.toList ≠ [] ∧ ∀ c ∈ n.toList, isNameChar c = true := by
  rw [isName, Bool.and_eq_true, Bool.not_eq_true', String.all_bool_eq, List.all_eq_true,
    String.isEmpty_eq_false_iff, ne_eq, ← String.toList_inj, String.toList_empty]

/-- Characters compare as their code points. -/
theorem le_char_iff {a b : Char} : a ≤ b ↔ a.toNat ≤ b.toNat :=
  Char.le_def.trans UInt32.le_iff_toNat_le

theorem eq_char_iff {a b : Char} : a = b ↔ a.toNat = b.toNat := Char.toNat_inj.symm

theorem isDigit_iff {c : Char} : c.isDigit = true ↔ 48 ≤ c.toNat ∧ c.toNat ≤ 57 :=
  Char.isDigit_iff_toNat

/-- The name characters, by code point. -/
theorem isNameChar_iff {c : Char} : isNameChar c = true ↔
    (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨ (97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨ c.toNat = 95 ∨
      (48 ≤ c.toNat ∧ c.toNat ≤ 57) ∨ c.toNat = 46 := by
  simp only [isNameChar, isWordStart, isLetter, le_char_iff, eq_char_iff, decide_eq_true_eq,
    isDigit_iff]
  simp
  omega

/-- The characters that start a word, by code point. -/
theorem isWordStart_iff {c : Char} : isWordStart c = true ↔
    (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨ (97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨ c.toNat = 95 := by
  simp only [isWordStart, isLetter, le_char_iff, eq_char_iff, decide_eq_true_eq]
  simp
  omega

theorem formatChars_ge : ∀ x ∈ formatChars, 0xad ≤ x.1 := by decide

/-- An escaped character is a control character or beyond ASCII. -/
theorem isEscaped_toNat {c : Char} (h : isEscaped c = true) : c.toNat < 32 ∨ 127 ≤ c.toNat := by
  simp only [isEscaped, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
    List.any_eq_true] at h
  rcases h with (((h | h) | h) | h) | ⟨x, hx, h, -⟩
  · omega
  · omega
  · omega
  · omega
  · have := formatChars_ge x hx; omega

/-- A printable ASCII character is not escaped. -/
theorem isEscaped_of_ascii {c : Char} (h₁ : 32 ≤ c.toNat) (h₂ : c.toNat < 127) :
    isEscaped c = false := by
  cases h : isEscaped c
  · rfl
  · have := isEscaped_toNat h; omega

/-- A printable ASCII character is allowed outside strings. -/
theorem allowed_of_ascii {c : Char} (h₁ : 32 ≤ c.toNat) (h₂ : c.toNat < 127) :
    allowedOutsideStrings c = true := by
  simp [allowedOutsideStrings, isEscaped_of_ascii h₁ h₂]

/-- A name character is printable ASCII. -/
theorem ascii_of_isNameChar {c : Char} (h : isNameChar c = true) : 32 ≤ c.toNat ∧ c.toNat < 127 := by
  rw [isNameChar_iff] at h
  omega

/-- A character that starts a word is no digit. -/
theorem isDigit_of_isWordStart {c : Char} (h : isWordStart c = true) : c.isDigit = false := by
  rw [isWordStart_iff] at h
  cases hd : c.isDigit
  · rfl
  · rw [isDigit_iff] at hd; omega

/-- A name character is no punctuation, `%`, `^`, `@`, `"`, `-`, whitespace
or `/`. -/
theorem ne_of_isNameChar {c : Char} (h : isNameChar c = true) :
    c ≠ '(' ∧ c ≠ ')' ∧ c ≠ '{' ∧ c ≠ '}' ∧ c ≠ ',' ∧ c ≠ ':' ∧ c ≠ '=' ∧ c ≠ '%' ∧ c ≠ '^' ∧
      c ≠ '@' ∧ c ≠ '"' ∧ c ≠ '-' ∧ c ≠ ' ' ∧ c ≠ '\t' ∧ c ≠ '\n' ∧ c ≠ '/' := by
  rw [isNameChar_iff] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro e; subst e; simp at h)

/-- A value name or a label: `%` or `^`, then the name, up to the first
character that is not a name character. -/
theorem readsToken_name {sigil : Char} (hσ : sigil = '%' ∨ sigil = '^') {n : String}
    (hn : isName n = true) {cs : List Char} (hs : Boundary cs) :
    ReadsToken sigil (n.toList ++ cs) cs (if sigil = '%' then .value n else .label n) := by
  intro p
  obtain ⟨hne, hall⟩ := isName_iff.mp hn
  obtain ⟨h₁, h₂⟩ := takeWhile_name hall hs
  have hne' : n.toList.isEmpty = false := by simpa using hne
  rcases hσ with rfl | rfl <;>
  · unfold lexToken
    simp (config := { decide := true }) only [ite_true, ite_false, h₁, hne', String.ofList_toList]
    simp only [h₂]
    exact ⟨_, by simp, rfl⟩

/-- A word, up to the first character that is not a name character. -/
theorem readsToken_word {c : Char} {cs₀ cs : List Char} (hc : isWordStart c = true)
    (h₀ : ∀ x ∈ cs₀, isNameChar x = true) (hs : Boundary cs) :
    ReadsToken c (cs₀ ++ cs) cs (.word (String.ofList (c :: cs₀))) := by
  intro p
  obtain ⟨h₁, h₂⟩ := takeWhile_name h₀ hs
  have hn : isNameChar c = true := by simp [isNameChar, hc]
  have hd := isDigit_of_isWordStart hc
  have ha := allowed_of_ascii (ascii_of_isNameChar hn).1 (ascii_of_isNameChar hn).2
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, -⟩ := ne_of_isNameChar hn
  unfold lexToken
  split <;> try (exfalso; revert hc; decide)
  simp only [ha, Bool.not_true, Bool.false_eq_true, ite_false, n8, n9, or_self, n10, n11, n12,
    hd, hc, ite_true, h₁, h₂]
  exact ⟨_, by simp, rfl⟩

/-! # Numbers and location references -/

/-- A character at the end of a token is no digit. -/
theorem isDigit_of_not_isNameChar {c : Char} (h : isNameChar c = false) : c.isDigit = false := by
  cases hd : c.isDigit
  · rfl
  · simp [isNameChar, hd] at h

/-- Digits are read up to the end of the token. -/
theorem takeWhile_digits {ds cs : List Char} (hd : ∀ x ∈ ds, x.isDigit = true) (hs : Boundary cs) :
    (ds ++ cs).takeWhile Char.isDigit = ds ∧ (ds ++ cs).dropWhile Char.isDigit = cs := by
  rw [List.takeWhile_append_of_pos hd, List.dropWhile_append_of_pos hd]
  match cs, hs with
  | [], _ => simp
  | c :: _, hs => simp [isDigit_of_not_isNameChar (hs c rfl)]

/-- The decimal digits of a number are digits. -/
theorem isDigit_of_toDigits {n : Nat} {c : Char} (h : c ∈ Nat.toDigits 10 n) : c.isDigit = true :=
  Nat.isDigit_of_mem_toDigits (by decide) (by decide) h

/-- The digits that the printer writes for a number are read whole. -/
theorem lexDigits_toDigits {n : Nat} {d : Char} {ds cs : List Char} (he : Nat.toDigits 10 n = d :: ds)
    (hs : Boundary cs) (p : TextPos) : ∃ hr, lexDigits d (ds ++ cs) p = .ok (d :: ds, ⟨cs, hr⟩) := by
  have hdig : ∀ x ∈ ds, x.isDigit = true := fun x hx =>
    isDigit_of_toDigits (he ▸ List.mem_cons_of_mem d hx)
  unfold lexDigits
  by_cases h0 : d = '0'
  · have hn : n = 0 := by
      apply Classical.byContradiction
      intro hn
      exact head_toDigits_ne_zero (b := 10) (by decide) (by decide) (Nat.pos_of_ne_zero hn)
        (by rw [he, h0]; rfl)
    subst hn h0
    rw [Nat.toDigits_zero] at he
    cases he
    simp only [ite_true, List.nil_append]
    match cs, hs with
    | [], _ => exact ⟨by simp, rfl⟩
    | c :: _, hs => exact ⟨by simp, by simp [hs c rfl]⟩
  · obtain ⟨h₁, h₂⟩ := takeWhile_digits hdig hs
    simp only [h0, ite_false, h₂, h₁]
    match cs, hs with
    | [], _ => exact ⟨by simp, rfl⟩
    | c :: _, hs => exact ⟨by simp, by simp [hs c rfl]⟩

/-- The first decimal digit of a number, and the others. -/
theorem toDigits_cons (n : Nat) : ∃ d ds, Nat.toDigits 10 n = d :: ds :=
  List.exists_cons_of_ne_nil Nat.toDigits_ne_nil

/-- A digit is a name character. -/
theorem isNameChar_of_isDigit {c : Char} (h : c.isDigit = true) : isNameChar c = true := by
  simp [isNameChar, h]

/-- A natural number, as an integer token. -/
theorem readsToken_nat {n : Nat} {d : Char} {ds cs : List Char} (he : Nat.toDigits 10 n = d :: ds)
    (hs : Boundary cs) : ReadsToken d (ds ++ cs) cs (.int n) := by
  intro p
  have hd : d.isDigit = true := isDigit_of_toDigits (he ▸ List.mem_cons_self ..)
  have hn := isNameChar_of_isDigit hd
  have ha := allowed_of_ascii (ascii_of_isNameChar hn).1 (ascii_of_isNameChar hn).2
  obtain ⟨-, -, -, -, -, -, -, n8, n9, n10, n11, n12, -⟩ := ne_of_isNameChar hn
  obtain ⟨hr, hl⟩ := lexDigits_toDigits he hs p
  unfold lexToken
  split <;> try (exfalso; revert hd; decide)
  simp only [ha, Bool.not_true, Bool.false_eq_true, ite_false, n8, n9, or_self, n10, n11, n12, hd,
    ite_true]
  unfold lexInt
  simp only [hl, ok_bind, ← he, digitsValue_toDigits]
  exact ⟨_, hr, rfl⟩

/-- A negative integer: `-`, then the digits of its magnitude. -/
theorem readsToken_neg {m : Nat} {d : Char} {ds cs : List Char} (he : Nat.toDigits 10 (m + 1) = d :: ds)
    (hs : Boundary cs) : ReadsToken '-' (d :: (ds ++ cs)) cs (.int (.negSucc m)) := by
  intro p
  have hd : d.isDigit = true := isDigit_of_toDigits (he ▸ List.mem_cons_self ..)
  have h0 : d ≠ '0' := fun h =>
    head_toDigits_ne_zero (b := 10) (by decide) (by decide) (Nat.succ_pos m) (by rw [he, h]; rfl)
  obtain ⟨hr, hl⟩ := lexDigits_toDigits he hs p
  rw [lexToken.eq_10 _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (fun h => by subst h; revert hd; decide) h0]
  simp (config := { decide := true }) only [ite_true, ite_false, hd]
  unfold lexInt
  simp only [hl, ok_bind, ← he, digitsValue_toDigits]
  exact ⟨_, by simp; omega, rfl⟩

/-- A location reference: `@`, then the digits of a number below `2^32`. -/
theorem readsToken_locRef {r : Nat} (hr : r < Location.limit) {d : Char} {ds cs : List Char}
    (he : Nat.toDigits 10 r = d :: ds) (hs : Boundary cs) :
    ReadsToken '@' (d :: (ds ++ cs)) cs (.locRef r) := by
  intro p
  have hd : d.isDigit = true := isDigit_of_toDigits (he ▸ List.mem_cons_self ..)
  obtain ⟨hr', hl⟩ := lexDigits_toDigits he hs (p.advance 1)
  unfold lexToken
  simp (config := { decide := true }) only [ite_true, ite_false]
  rw [lexAt]
  simp only [hd, ite_true, hl, ok_bind, ← he, digitsValue_toDigits, hr]
  exact ⟨_, by simp; omega, rfl⟩

end Fir.Text
