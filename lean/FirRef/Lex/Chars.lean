import Fir.Text.Lex
import FirRef.Except

/-!
`fir-ref` lexes a text over positions in the `String`, without the list of
its characters that the spec's lexer reads (`String.toList`). `chars p` is
the characters from the position `p` on, as that list: proofs and measures
use it, and code never builds it. The functions here walk a position as the
spec's lexer walks its list: `skipWhileP` is `List.dropWhile`, and
`takeWhileP` is `List.takeWhile`. `commentP` scans a comment's body as the
spec's lexer does with `firstDisallowed` and `utf8Len`, without a list of
its characters.
-/

namespace FirRef

open Fir Fir.Text

variable {s : String}

/-- The characters of `s` from the position `p` on. -/
def chars (p : s.Pos) : List Char := (s.sliceFrom p).copy.toList

theorem chars_endPos (s : String) : chars s.endPos = [] := by
  simp [chars, String.copy_sliceFrom_startPos]

theorem chars_next {p : s.Pos} (h : p ≠ s.endPos) : chars p = p.get h :: chars (p.next h) := by
  unfold chars
  rw [p.splits.eq_right (String.Pos.splits_next_right p h)]
  simp [String.toList_append]

theorem chars_startPos (s : String) : chars s.startPos = s.toList := by
  simp [chars, String.sliceFrom_startPos]

theorem chars_eq_nil {p : s.Pos} : chars p = [] ↔ p = s.endPos := by
  constructor
  · intro h
    by_cases hne : p = s.endPos
    · exact hne
    · rw [chars_next hne] at h
      cases h
  · rintro rfl
    exact chars_endPos s

theorem length_chars_next {p : s.Pos} (h : p ≠ s.endPos) :
    (chars (p.next h)).length < (chars p).length := by
  rw [chars_next h]
  simp

/-- The first position from `p` on whose character fails `f`, or the end. -/
def skipWhileP (f : Char → Bool) (p : s.Pos) : s.Pos :=
  if h : p = s.endPos then p
  else if f (p.get h) then skipWhileP f (p.next h) else p
termination_by (chars p).length
decreasing_by exact length_chars_next h

theorem chars_skipWhileP (f : Char → Bool) (p : s.Pos) :
    chars (skipWhileP f p) = (chars p).dropWhile f := by
  fun_induction skipWhileP f p with
  | case1 => rw [chars_endPos]; rfl
  | case2 p h hf ih => rw [ih, chars_next h, List.dropWhile_cons_of_pos hf]
  | case3 p h hf => rw [chars_next h, List.dropWhile_cons_of_neg hf]

/-- The characters from `p` on that satisfy `f`, up to the first that does
not; `acc` holds those already taken, last first. -/
def takeWhileP (f : Char → Bool) (p : s.Pos) (acc : List Char) : List Char :=
  if h : p = s.endPos then acc.reverse
  else if f (p.get h) then takeWhileP f (p.next h) (p.get h :: acc) else acc.reverse
termination_by (chars p).length
decreasing_by exact length_chars_next h

theorem takeWhileP_eq (f : Char → Bool) (p : s.Pos) (acc : List Char) :
    takeWhileP f p acc = acc.reverse ++ (chars p).takeWhile f := by
  fun_induction takeWhileP f p acc with
  | case1 acc => rw [chars_endPos]; simp
  | case2 p acc h hf ih => rw [ih, chars_next h, List.takeWhile_cons_of_pos hf]; simp
  | case3 p acc h hf => rw [chars_next h, List.takeWhile_cons_of_neg hf]; simp

/-- The next character at `p` and the position after it, if any. It is
inlined, so that the code of its callers builds neither the option nor the
pair. -/
@[inline] def peekP (p : s.Pos) : Option (Char × s.Pos) :=
  if h : p = s.endPos then none else some (p.get h, p.next h)

theorem chars_of_peekP {p q : s.Pos} {c : Char} (h : peekP p = some (c, q)) :
    chars p = c :: chars q := by
  unfold peekP at h
  split at h
  · cases h
  · rename_i hne
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact chars_next hne

theorem chars_of_peekP_none {p : s.Pos} (h : peekP p = none) : chars p = [] := by
  unfold peekP at h
  split at h
  · rename_i he
    rw [he, chars_endPos]
  · cases h

theorem length_lt_of_peekP {p q : s.Pos} {c : Char} (h : peekP p = some (c, q)) :
    (chars q).length < (chars p).length := by
  rw [chars_of_peekP h]
  simp

theorem skipWhileP_endPos (f : Char → Bool) : skipWhileP f s.endPos = s.endPos := by
  rw [skipWhileP]
  simp

theorem skipWhileP_of_pos {f : Char → Bool} {p : s.Pos} (h : p ≠ s.endPos)
    (hf : f (p.get h) = true) : skipWhileP f p = skipWhileP f (p.next h) := by
  rw [skipWhileP]
  simp [h, hf]

theorem skipWhileP_of_neg {f : Char → Bool} {p : s.Pos} (h : p ≠ s.endPos)
    (hf : ¬f (p.get h) = true) : skipWhileP f p = p := by
  rw [skipWhileP]
  simp [h, hf]

/-- Scans the body of a comment from `i`, `n` bytes into it, without a list
of its characters: the first character that is not allowed outside
strings, with its offset in bytes, or the body's width in bytes and the
position of the line feed or the end of the text after it. Its only call
to itself is a tail call. -/
def commentP (i : s.Pos) (n : Nat) : (Char × Nat) ⊕ (Nat × s.Pos) :=
  if h : i = s.endPos then .inr (n, i)
  else if notLineFeed (i.get h) then
    if allowedOutsideStrings (i.get h) then commentP (i.next h) (n + (i.get h).utf8Size)
    else .inl (i.get h, n)
  else .inr (n, i)
termination_by (chars i).length
decreasing_by exact length_chars_next h

/-- `commentP` finds what the spec's lexer finds in a comment's body, the
characters up to the next line feed: `firstDisallowed`, then `utf8Len` and
`List.dropWhile`. -/
theorem commentP_eq (i : s.Pos) (n : Nat) :
    commentP i n = match firstDisallowed ((chars i).takeWhile notLineFeed) n with
      | some x => .inl x
      | none => .inr (n + utf8Len ((chars i).takeWhile notLineFeed), skipWhileP notLineFeed i) := by
  fun_induction commentP i n with
  | case1 n =>
    simp [chars_endPos, firstDisallowed, utf8Len, skipWhileP_endPos]
  | case2 i n h hf ha ih =>
    rw [ih, chars_next h, List.takeWhile_cons_of_pos hf, skipWhileP_of_pos h hf]
    simp only [firstDisallowed, ha, ↓reduceIte]
    split <;> simp [utf8Len, Nat.add_assoc]
  | case3 i n h hf ha =>
    rw [chars_next h, List.takeWhile_cons_of_pos hf]
    simp [firstDisallowed, ha]
  | case4 i n h hf =>
    rw [chars_next h, List.takeWhile_cons_of_neg hf, skipWhileP_of_neg h hf]
    simp [firstDisallowed, utf8Len]

theorem commentP_inl {i : s.Pos} {n : Nat} {x : Char × Nat} (h : commentP i n = .inl x) :
    firstDisallowed ((chars i).takeWhile notLineFeed) n = some x := by
  rw [commentP_eq] at h
  split at h
  · rename_i y hy
    cases h
    exact hy
  · cases h

theorem commentP_inr {i j : s.Pos} {n m : Nat} (h : commentP i n = .inr (m, j)) :
    firstDisallowed ((chars i).takeWhile notLineFeed) n = none ∧
      m = n + utf8Len ((chars i).takeWhile notLineFeed) ∧ j = skipWhileP notLineFeed i := by
  rw [commentP_eq] at h
  split at h
  · cases h
  · rename_i hy
    simp only [Sum.inr.injEq, Prod.mk.injEq] at h
    exact ⟨hy, h.1.symm, h.2.symm⟩

theorem commentP_le {i j : s.Pos} {n m : Nat} (h : commentP i n = .inr (m, j)) :
    (chars j).length ≤ (chars i).length := by
  rw [(commentP_inr h).2.2, chars_skipWhileP]
  exact length_dropWhile_le notLineFeed (chars i)

end FirRef
