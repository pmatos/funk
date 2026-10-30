import Std.Data.HashMap
import Std.Data.HashSet

/-!
The check looks names up in hash tables, so that it takes time close to
linear in the size of a module, and it walks every list in a loop that takes
no stack per element. Dominance is the exception to the time: the check
decides it with a search of the function's graph for each use whose
definition is in another block, so that part is quadratic in the worst case. The four tools below are those tables and loops, each
with the theorem that says what it computes in terms of plain lists:

* `firsts` keeps the first value of each key, as `List.find?` finds it;
* `grouped` collects every value of each key;
* `repeats` lists each element that repeats an earlier one, so it is empty
  exactly when the list has no duplicates (`List.Nodup`);
* `sameLists` compares two lists.
-/

namespace Fir

variable {α β : Type}

section
variable [BEq α] [Hashable α]

/-- The first value of each key in a list of pairs. -/
def firsts (l : List (α × β)) : Std.HashMap α β :=
  l.foldl (fun m p => m.insertIfNew p.1 p.2) ∅

/-- Every value of each key in a list of pairs, where each pair holds a list
of values. -/
def grouped (l : List (α × List β)) : Std.HashMap α (List β) :=
  l.foldl (fun m p => m.insert p.1 (p.2 ++ m.getD p.1 [])) ∅

/-- The elements of `l` that repeat an earlier one, in order, once for each
time they repeat. `seen` holds the elements before them. -/
def repeatsFrom (seen : Std.HashSet α) (acc : List α) : List α → List α
  | [] => acc.reverse
  | x :: xs =>
    if seen.contains x then repeatsFrom seen (x :: acc) xs
    else repeatsFrom (seen.insert x) acc xs

/-- The elements of a list that repeat an earlier one. -/
def repeats (l : List α) : List α := repeatsFrom ∅ [] l
end

/-- Whether two lists are equal, compared in a loop. -/
def sameLists [DecidableEq α] : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => if a = b then sameLists as bs else false
  | _, _ => false

theorem sameLists_iff [DecidableEq α] {l₁ l₂ : List α} : sameLists l₁ l₂ = true ↔ l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp [sameLists]
  | cons a as ih =>
    cases l₂ with
    | nil => simp [sameLists]
    | cons b bs => by_cases h : a = b <;> simp [sameLists, h, ih]

variable [BEq α] [Hashable α] [LawfulBEq α]

theorem getElem?_foldl_insertIfNew (l : List (α × β)) (m : Std.HashMap α β) (k : α) :
    (l.foldl (fun m p => m.insertIfNew p.1 p.2) m)[k]? =
      (m[k]?).or ((l.find? (·.1 == k)).map (·.2)) := by
  induction l generalizing m with
  | nil => simp
  | cons p l ih =>
    rw [List.foldl_cons, ih, Std.HashMap.getElem?_insertIfNew, List.find?_cons]
    by_cases h : p.1 = k
    · subst h
      cases hm : m[p.1]? with
      | none => simp [Std.HashMap.mem_iff_isSome_getElem?, hm]
      | some v => simp [Std.HashMap.mem_iff_isSome_getElem?, hm]
    · have : (p.1 == k) = false := by simpa using h
      simp [this]

theorem getElem?_firsts (l : List (α × β)) (k : α) :
    (firsts l)[k]? = (l.find? (·.1 == k)).map (·.2) := by
  simp [firsts, getElem?_foldl_insertIfNew]

theorem mem_getD_foldl_grouped (l : List (α × List β)) (m : Std.HashMap α (List β)) (k : α)
    (v : β) : v ∈ (l.foldl (fun m p => m.insert p.1 (p.2 ++ m.getD p.1 [])) m).getD k [] ↔
      v ∈ m.getD k [] ∨ ∃ p ∈ l, p.1 = k ∧ v ∈ p.2 := by
  induction l generalizing m with
  | nil => simp
  | cons p l ih =>
    rw [List.foldl_cons, ih, Std.HashMap.getD_insert]
    by_cases h : p.1 = k
    · subst h; simp; grind
    · have : (p.1 == k) = false := by simpa using h
      simp [this, h]

theorem contains_foldl_grouped (l : List (α × List β)) (m : Std.HashMap α (List β)) (k : α) :
    (l.foldl (fun m p => m.insert p.1 (p.2 ++ m.getD p.1 [])) m).contains k = true ↔
      m.contains k = true ∨ ∃ p ∈ l, p.1 = k := by
  induction l generalizing m with
  | nil => simp
  | cons p l ih =>
    rw [List.foldl_cons, ih, Std.HashMap.contains_insert]
    simp only [Bool.or_eq_true, beq_iff_eq, List.mem_cons, exists_eq_or_imp]
    grind

theorem mem_getD_grouped (l : List (α × List β)) (k : α) (v : β) :
    v ∈ (grouped l).getD k [] ↔ ∃ p ∈ l, p.1 = k ∧ v ∈ p.2 := by
  simp [grouped, mem_getD_foldl_grouped]

theorem contains_grouped (l : List (α × List β)) (k : α) :
    (grouped l).contains k = true ↔ ∃ p ∈ l, p.1 = k := by
  rw [grouped, contains_foldl_grouped]
  simp

theorem repeatsFrom_eq_nil (seen : Std.HashSet α) (acc l : List α) :
    repeatsFrom seen acc l = [] ↔ acc = [] ∧ (∀ x ∈ l, x ∉ seen) ∧ l.Nodup := by
  induction l generalizing seen acc with
  | nil => simp [repeatsFrom]
  | cons x xs ih =>
    simp only [repeatsFrom]
    split
    · rename_i h
      rw [ih]
      simp_all
    · rename_i h
      have hx : x ∉ seen := by simpa using h
      rw [ih]
      simp only [Std.HashSet.mem_insert, beq_iff_eq, not_or, List.nodup_cons, List.mem_cons,
        forall_eq_or_imp]
      constructor
      · rintro ⟨rfl, hs, hn⟩
        exact ⟨rfl, ⟨hx, fun y hy => (hs y hy).2⟩, fun hm => (hs x hm).1 rfl, hn⟩
      · rintro ⟨rfl, ⟨_, hs⟩, hm, hn⟩
        exact ⟨rfl, fun y hy => ⟨fun e => hm (e ▸ hy), hs y hy⟩, hn⟩

theorem repeats_eq_nil (l : List α) : repeats l = [] ↔ l.Nodup := by
  simp [repeats, repeatsFrom_eq_nil]

end Fir
