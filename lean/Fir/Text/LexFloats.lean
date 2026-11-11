import Fir.Text.LexTokens

/-!
# Reading printed float literals

The printer writes a float literal as it is held (ADR-2026-11-11-1438): a
decimal as `-`, if negative, the digits of its whole part, `.`, its
fraction and, if it has one, `e` and its exponent; hexadecimal bits as `0x`
and their digits. The lexer reads each back as itself whenever it is
followed by the end of a token: the whole part as the digits of a number,
the fraction up to the first character that is no digit, which is `e` or
the end, the exponent as the digits of an integer, and the hexadecimal
digits up to the end. The last theorems read each kind of literal from its
first character, as `lexToken` does.
-/

namespace Fir.Text

/-- The characters of a float literal's exponent part. -/
def expChars : Option Int → List Char
  | some x => 'e' :: (printInt x).toList
  | none => []

theorem lexEnd_boundary {cs : List Char} (hs : Boundary cs) (p : TextPos) : lexEnd cs p = .ok () := by
  unfold lexEnd
  match cs, hs with
  | [], _ => rfl
  | c :: _, hs => simp [hs c rfl]

/-- A character at the end of a token is not `e`, `x`, `.` or a hexadecimal digit. -/
theorem ne_of_boundary {c : Char} {cs : List Char} (hs : Boundary (c :: cs)) :
    c ≠ 'e' ∧ c ≠ 'x' ∧ c ≠ '.' ∧ isHexDigit c = false ∧ c.isDigit = false := by
  have h := hs c rfl
  refine ⟨?_, ?_, ?_, ?_, isDigit_of_not_isNameChar h⟩
  · rintro rfl; simp (config := { decide := true }) at h
  · rintro rfl; simp (config := { decide := true }) at h
  · rintro rfl; simp (config := { decide := true }) at h
  · cases hx : isHexDigit c
    · rfl
    · simp only [isHexDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hx
      have h' : ¬ (isNameChar c = true) := by simp [h]
      rw [isNameChar_iff] at h'
      simp only [le_char_iff, isDigit_iff] at hx
      simp at hx
      omega

theorem lexExponent_spells (exp : Option Int) {cs : List Char} (hs : Boundary cs) (p : TextPos) :
    ∃ h, lexExponent (expChars exp ++ cs) p = .ok (exp, ⟨cs, h⟩) := by
  match exp with
  | none =>
    refine ⟨by simp [expChars], ?_⟩
    simp only [expChars, List.nil_append]
    match cs, hs with
    | [], _ => rfl
    | c :: r, hs =>
      obtain ⟨he, -, -, -, -⟩ := ne_of_boundary hs
      rw [lexExponent.eq_3 _ _ (fun _ _ h => by simp at h; exact he h.1)
        (fun _ _ h => by simp at h; exact he h.1)]
      simp only [lexEnd, hs c rfl, Bool.false_eq_true, ite_false]
      rfl
  | some (.ofNat n) =>
    obtain ⟨d, ds, he⟩ := toDigits_cons n
    have hd : d.isDigit = true := isDigit_of_toDigits (he ▸ List.mem_cons_self ..)
    have hm : d ≠ '-' := fun h => by subst h; revert hd; decide
    obtain ⟨hr, hl⟩ := lexDigits_toDigits he hs p
    have hc : expChars (some (.ofNat n)) ++ cs = 'e' :: d :: (ds ++ cs) := by
      simp only [expChars, printInt]
      rw [show (toString (Int.ofNat n)).toList = Nat.toDigits 10 n from Nat.toList_repr, he]
      rfl
    rw [hc, lexExponent.eq_2 _ _ _ (fun _ _ h _ => hm h)]
    simp only [hd, ite_true, hl, ok_bind, ← he, digitsValue_toDigits]
    exact ⟨by simp; omega, rfl⟩
  | some (.negSucc m) =>
    obtain ⟨d, ds, he⟩ := toDigits_cons (m + 1)
    have hd : d.isDigit = true := isDigit_of_toDigits (he ▸ List.mem_cons_self ..)
    have h0 : d ≠ '0' := fun h =>
      head_toDigits_ne_zero (b := 10) (by decide) (by decide) (Nat.succ_pos m) (by rw [he, h]; rfl)
    obtain ⟨hr, hl⟩ := lexDigits_toDigits he hs p
    have hc : expChars (some (.negSucc m)) ++ cs = 'e' :: '-' :: d :: (ds ++ cs) := by
      simp only [expChars, printInt]
      rw [show (toString (Int.negSucc m)).toList = '-' :: Nat.toDigits 10 (m + 1) from
        (String.toList_append (s := "-") (t := Nat.repr (m + 1))).trans (by simp), he]
      simp
    rw [hc, lexExponent.eq_1]
    simp only [h0, ite_false, hd, ite_true, hl, ok_bind, ← he, digitsValue_toDigits]
    exact ⟨by simp; omega, rfl⟩


/-- What follows a fraction starts with no digit. -/
theorem notDigit_expChars (exp : Option Int) {cs : List Char} (hs : Boundary cs) :
    ∀ c ∈ (expChars exp ++ cs).head?, c.isDigit = false := by
  match exp with
  | some x => simp [expChars]
  | none =>
    simp only [expChars, List.nil_append]
    match cs, hs with
    | [], _ => simp
    | c :: _, hs => simpa using isDigit_of_not_isNameChar (hs c rfl)

theorem takeWhile_digits' {ds cs : List Char} (hd : ∀ x ∈ ds, x.isDigit = true)
    (hs : ∀ c ∈ cs.head?, c.isDigit = false) :
    (ds ++ cs).takeWhile Char.isDigit = ds ∧ (ds ++ cs).dropWhile Char.isDigit = cs := by
  rw [List.takeWhile_append_of_pos hd, List.dropWhile_append_of_pos hd]
  match cs, hs with
  | [], _ => simp
  | c :: _, hs => simp [hs c rfl]

theorem lexFraction_spells (neg : Bool) (whole : Nat) {f : Char} {fs : List Char}
    (hf : ∀ x ∈ fs, x.isDigit = true) (exp : Option Int) {cs : List Char} (hs : Boundary cs)
    (p : TextPos) : ∃ h q, lexFraction neg whole f (fs ++ (expChars exp ++ cs)) p =
      .ok (.float (.dec neg whole (f :: fs) exp), ⟨cs, h⟩, q) := by
  obtain ⟨h₁, h₂⟩ := takeWhile_digits' hf (notDigit_expChars exp hs)
  have key : ∀ L, L = expChars exp ++ cs → ∃ h, lexExponent L p = .ok (exp, ⟨cs, h⟩) := by
    rintro L rfl
    exact lexExponent_spells exp hs p
  obtain ⟨he, hl⟩ := key _ h₂
  unfold lexFraction
  rw [hl, ok_bind]
  simp only [h₁]
  exact ⟨Nat.le_trans he (length_dropWhile_le _ _), _, rfl⟩


/-- The whole part of a printed number is all of its digits, before a
character that is no digit. -/
theorem whole_toDigits {n : Nat} {d : Char} {ds cs : List Char} (he : Nat.toDigits 10 n = d :: ds)
    (hs : ∀ c ∈ cs.head?, c.isDigit = false) :
    afterWhole d (ds ++ cs) = cs ∧ wholeValue d (ds ++ cs) = n := by
  unfold afterWhole wholeValue
  by_cases h0 : d = '0'
  · have hn : n = 0 := by
      apply Classical.byContradiction
      intro hn
      exact head_toDigits_ne_zero (b := 10) (by decide) (by decide) (Nat.pos_of_ne_zero hn)
        (by rw [he, h0]; rfl)
    subst hn h0
    rw [Nat.toDigits_zero] at he
    cases he
    simp
  · have hdig : ∀ x ∈ ds, x.isDigit = true := fun x hx =>
      isDigit_of_toDigits (he ▸ List.mem_cons_of_mem d hx)
    obtain ⟨h₁, h₂⟩ := takeWhile_digits' hdig hs
    simp only [h0, ite_false, h₁, h₂, ← he, digitsValue_toDigits, and_self]

theorem lexFloat_dec (neg : Bool) {n : Nat} {d : Char} {ds : List Char} (he : Nat.toDigits 10 n = d :: ds)
    {f : Char} {fs : List Char} (hf : f.isDigit = true) (hfs : ∀ x ∈ fs, x.isDigit = true)
    (exp : Option Int) {cs : List Char} (hs : Boundary cs) (p : TextPos) :
    ∃ h q, lexFloat neg d (ds ++ '.' :: f :: (fs ++ (expChars exp ++ cs))) p =
      some (.ok (.float (.dec neg n (f :: fs) exp), ⟨cs, h⟩, q)) := by
  obtain ⟨hw, hv⟩ := whole_toDigits he (cs := '.' :: f :: (fs ++ (expChars exp ++ cs))) (by simp)
  obtain ⟨h, q, hl⟩ := lexFraction_spells neg n (f := f) hfs exp hs p
  unfold lexFloat
  split
  · rename_i c r heq
    rw [hw] at heq
    simp only [List.cons.injEq] at heq
    obtain ⟨-, rfl, rfl⟩ := heq
    simp only [hf, ite_true, hv, hl]
    exact ⟨by simp at h ⊢; omega, _, rfl⟩
  · rename_i r heq
    rw [hw] at heq
    simp at heq
  · rename_i hx _
    rw [hw] at hx
    exact absurd rfl (hx f (fs ++ (expChars exp ++ cs)))

theorem lexHex_spells {ds : List Char} (hne : ds ≠ []) (hd : ∀ x ∈ ds, isHexDigit x = true)
    {cs : List Char} (hs : Boundary cs) (p : TextPos) :
    ∃ h q, lexHex (ds ++ cs) p = .ok (.float (.hex ds), ⟨cs, h⟩, q) := by
  have h₁ : (ds ++ cs).takeWhile isHexDigit = ds ∧ (ds ++ cs).dropWhile isHexDigit = cs := by
    rw [List.takeWhile_append_of_pos hd, List.dropWhile_append_of_pos hd]
    match cs, hs with
    | [], _ => simp
    | c :: _, hs => simp [(ne_of_boundary hs).2.2.2.1]
  have hne' : ds.isEmpty = false := by simpa using hne
  unfold lexHex
  simp only [h₁.1, hne', Bool.false_eq_true, ite_false]
  have key : ∀ L (hL : L.length ≤ (ds ++ cs).length), L = cs → ∃ h q,
      Except.map (fun _ => (Tok.float (.hex ds), (⟨L, hL⟩ : Left (ds ++ cs)),
        p.advance (2 + ds.length))) (lexEnd L p) = .ok (.float (.hex ds), ⟨cs, h⟩, q) := by
    rintro L hL rfl
    rw [lexEnd_boundary hs]
    exact ⟨hL, _, rfl⟩
  exact key _ _ h₁.2

theorem lexFloat_hex {ds : List Char} (hne : ds ≠ []) (hd : ∀ x ∈ ds, isHexDigit x = true)
    {cs : List Char} (hs : Boundary cs) (p : TextPos) :
    ∃ h q, lexFloat false '0' ('x' :: (ds ++ cs)) p = some (.ok (.float (.hex ds), ⟨cs, h⟩, q)) := by
  obtain ⟨h, q, hl⟩ := lexHex_spells hne hd hs p
  unfold lexFloat
  split
  · rename_i heq
    simp [afterWhole] at heq
  · rename_i r heq
    simp only [afterWhole, ite_true, List.cons.injEq, true_and] at heq
    subst heq
    simp only [and_self, ite_true, hl]
    exact ⟨by simp at h ⊢; omega, _, rfl⟩
  · simp_all [afterWhole]


/-- A decimal float literal with no `-`, from its first digit. -/
theorem readsToken_dec {n : Nat} {d : Char} {ds : List Char} (he : Nat.toDigits 10 n = d :: ds)
    {f : Char} {fs : List Char} (hf : f.isDigit = true) (hfs : ∀ x ∈ fs, x.isDigit = true)
    (exp : Option Int) {cs : List Char} (hs : Boundary cs) :
    ReadsToken d (ds ++ '.' :: f :: (fs ++ (expChars exp ++ cs))) cs (.float (.dec false n (f :: fs) exp)) := by
  intro p
  have hd : d.isDigit = true := isDigit_of_toDigits (he ▸ List.mem_cons_self ..)
  have hn := isNameChar_of_isDigit hd
  have ha := allowed_of_ascii (ascii_of_isNameChar hn).1 (ascii_of_isNameChar hn).2
  obtain ⟨-, -, -, -, -, -, -, n8, n9, n10, n11, n12, -⟩ := ne_of_isNameChar hn
  obtain ⟨hr, q, hl⟩ := lexFloat_dec false he hf hfs exp hs p
  unfold lexToken
  split <;> try (exfalso; revert hd; decide)
  simp only [ha, Bool.not_true, Bool.false_eq_true, ite_false, n8, n9, or_self, n10, n11, n12, hd,
    ite_true]
  unfold lexNumber
  rw [hl]
  exact ⟨_, hr, rfl⟩

/-- A decimal float literal with `-`, from the `-`. -/
theorem readsToken_negDec {n : Nat} {d : Char} {ds : List Char} (he : Nat.toDigits 10 n = d :: ds)
    {f : Char} {fs : List Char} (hf : f.isDigit = true) (hfs : ∀ x ∈ fs, x.isDigit = true)
    (exp : Option Int) {cs : List Char} (hs : Boundary cs) :
    ReadsToken '-' (d :: (ds ++ '.' :: f :: (fs ++ (expChars exp ++ cs)))) cs
      (.float (.dec true n (f :: fs) exp)) := by
  intro p
  have hd : d.isDigit = true := isDigit_of_toDigits (he ▸ List.mem_cons_self ..)
  obtain ⟨hr, q, hl⟩ := lexFloat_dec true he hf hfs exp hs p
  by_cases h0 : d = '0'
  · subst h0
    rw [lexToken.eq_9 _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
    simp (config := { decide := true }) only [ite_true, ite_false, hl, ok_bind]
    exact ⟨_, by simp at hr ⊢; omega, rfl⟩
  · rw [lexToken.eq_10 _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (fun h => by subst h; revert hd; decide) h0]
    simp (config := { decide := true }) only [ite_true, ite_false, hd]
    unfold lexNumber
    rw [hl]
    exact ⟨_, by simp at hr ⊢; omega, rfl⟩

/-- Hexadecimal bits, from the `0`. -/
theorem readsToken_hex {ds : List Char} (hne : ds ≠ []) (hd : ∀ x ∈ ds, isHexDigit x = true)
    {cs : List Char} (hs : Boundary cs) : ReadsToken '0' ('x' :: (ds ++ cs)) cs (.float (.hex ds)) := by
  intro p
  obtain ⟨hr, q, hl⟩ := lexFloat_hex hne hd hs p
  unfold lexToken
  simp (config := { decide := true }) only [ite_true, ite_false]
  unfold lexNumber
  rw [hl]
  exact ⟨_, hr, rfl⟩

end Fir.Text
