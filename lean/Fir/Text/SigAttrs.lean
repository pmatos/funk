import Fir.Syntax.Module
import Fir.Syntax.FuncAttrs

/-!
# The attributes of a signature

A function holds the attributes of its parameters and of its results as
lists that leave out the empty lists at their end (`AttrsTrimmed`), so a
function with none holds `[]`. The text writes the attributes of every
place (`padAttrs`), and decoding leaves out the empty lists at the end
again (`trimAttrs`). These laws say that the two undo each other, and that
what decoding gives has the form a function holds.
-/

namespace Fir

/-- The attributes of each of `n` places, from a list of at most `n`, are
that list, then empty lists. -/
theorem padAttrs_eq {n : Nat} {as : List (List Attr)} (h : as.length ≤ n) :
    padAttrs n as = as ++ List.replicate (n - as.length) [] := by
  apply List.ext_getElem
  · simp [padAttrs]; omega
  · intro i h₁ h₂
    simp only [padAttrs, List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
    by_cases hi : i < as.length
    · rw [List.getElem_append_left hi, List.getElem?_eq_getElem hi]; rfl
    · rw [List.getElem_append_right (by omega), List.getElem?_eq_none (by omega)]
      simp

/-- There is one list of attributes for each place. -/
@[simp] theorem length_padAttrs (n : Nat) (as : List (List Attr)) : (padAttrs n as).length = n := by
  simp [padAttrs]

/-- Leaving out the empty lists at the end of a list that ends in empty
lists leaves them out of the list before them. -/
theorem trimAttrs_append_replicate (as : List (List Attr)) (k : Nat) :
    trimAttrs (as ++ List.replicate k []) = trimAttrs as := by
  unfold trimAttrs
  rw [List.reverse_append, List.reverse_replicate]
  congr 1
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.cons_append, List.dropWhile_cons]; simp [ih]

/-- A list that does not end in an empty list leaves nothing out. -/
theorem trimAttrs_of_getLast {as : List (List Attr)} (h : ∀ a ∈ as.getLast?, a.isEmpty = false) :
    trimAttrs as = as := by
  unfold trimAttrs
  rcases List.eq_nil_or_concat as with rfl | ⟨l, a, rfl⟩
  · rfl
  · have ha : a.isEmpty = false := h a (by simp)
    rw [List.concat_eq_append, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.dropWhile_cons]
    simp [ha]

/-- Decoding the attributes that the text writes for each of `n` places
gives back the list a function holds. -/
theorem trimAttrs_padAttrs {n : Nat} {as : List (List Attr)} (h : AttrsTrimmed n as) :
    trimAttrs (padAttrs n as) = as := by
  rw [padAttrs_eq h.1, trimAttrs_append_replicate, trimAttrs_of_getLast h.2]

/-- Leaving out the empty lists at the end of a list gives a list of no more
places that does not end in an empty list. -/
theorem trimAttrs_trimmed (as : List (List Attr)) :
    AttrsTrimmed as.length (trimAttrs as) := by
  unfold trimAttrs AttrsTrimmed
  refine ⟨by simpa using (List.dropWhile_suffix (p := List.isEmpty) (l := as.reverse)).sublist.length_le, ?_⟩
  intro a ha
  rw [List.getLast?_reverse] at ha
  have hh := List.head?_dropWhile_not (fun x : List Attr => x.isEmpty) as.reverse
  rw [ha] at hh
  simpa using hh

/-- A list of attributes for each place that is not empty is its places but
the last, then the last place's. -/
theorem dropLast_append_getLast {as : List (List Attr)} (h : as ≠ []) :
    as.dropLast ++ [as.getLast?.getD []] = as := by
  rw [List.getLast?_eq_some_getLast h, Option.getD_some, List.dropLast_concat_getLast]

/-- Each list of attributes for a place is one of the lists given, or
empty. -/
theorem mem_padAttrs {n : Nat} {as : List (List Attr)} {a : List Attr} (h : a ∈ padAttrs n as) :
    a ∈ as ∨ a = [] := by
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp h
  rw [List.getD_eq_getElem?_getD]
  rcases hi : as[i]? with _ | b
  · exact .inr rfl
  · exact .inl (List.mem_of_getElem? hi)

/-- Each list that decoding keeps is one of the lists it was given. -/
theorem mem_of_mem_trimAttrs {as : List (List Attr)} {a : List Attr} (h : a ∈ trimAttrs as) :
    a ∈ as := by
  unfold trimAttrs at h
  exact List.mem_reverse.mp ((List.dropWhile_suffix _).subset (List.mem_reverse.mp h))

/-- Each list of attributes that a function holds for its places is the
attributes of one of them. -/
theorem mem_zip_padAttrs {α : Type} {xs : List α} {as : List (List Attr)}
    (h : as.length ≤ xs.length) {a : List Attr} (ha : a ∈ as) :
    ∃ x, (x, a) ∈ xs.zip (padAttrs xs.length as) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  refine ⟨xs[i]'(by omega), List.mem_iff_getElem.mpr ⟨i, by simp; omega, ?_⟩⟩
  simp [padAttrs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

end Fir
