import Std.Data.String.ToNat
import Fir.Core.Text
import Fir.Core.Validation
import Fir.Text.RoundTrip

/-!
The core dialect's types read back from how they are written, and only
from it: `i` and a width, an alias of a float format, `float(e, m)`, `ptr`
or `ptr(N)`.
Every valid type is written as a type. The next section uses these facts
for the laws of the core dialect's text.
-/

namespace Fir.Core

/-! # Types -/

/-- The characters of `iN`. -/
theorem toList_int_attr (w : Nat) : ("i" ++ toString w).toList = 'i' :: Nat.toDigits 10 w := by
  simp [String.toList_append, toString, Nat.toList_repr]

/-- An alias names the format it is the alias of. -/
theorem aliasFormat_of_floatAlias {e m : Nat} {n : String} (h : floatAlias e m = some n) :
    aliasFormat n = some (e, m) := by
  unfold floatAlias at h
  split at h <;> cases h <;> rfl

/-- The format that an alias names has that alias. -/
theorem floatAlias_of_aliasFormat {n : String} {e m : Nat} (h : aliasFormat n = some (e, m)) :
    floatAlias e m = some n := by
  unfold aliasFormat at h
  split at h <;> cases h <;> rfl

/-- Each alias reads back as the format it names. -/
theorem Ty.decode_alias {n : String} {e m : Nat} (h : aliasFormat n = some (e, m)) :
    Ty.decode (.word n) = some (.float e m) := by
  unfold aliasFormat at h
  split at h <;> cases h <;> rfl

/-- `float(e, m)` reads back as the format it writes when the format has no
alias and fits the width limit. -/
theorem Ty.decode_float {e m : Nat} (ha : floatAlias e m = none)
    (hw : floatWidth e m ≤ maxWidth) :
    Ty.decode (.app "float" [.int e, .int m]) = some (.float e m) := by
  have : (e : Int) + m + 1 ≤ (maxWidth : Int) := by unfold floatWidth at hw; omega
  simp [Ty.decode, decodeFloat, ha, this]

/-- `ptr(N)` reads back as the pointer type it writes, for every memory
other than the default one, up to `maxMemory`. -/
theorem Ty.decode_ptr {n : Nat} (h : n + 1 ≤ maxMemory) :
    Ty.decode (Ty.ptr (n + 1)).attr = some (.ptr (n + 1)) := by
  have hc : (1 : Int) ≤ (n : Int) + 1 ∧ (n : Int) + 1 ≤ maxMemory := by omega
  simp only [Ty.attr, Ty.decode, decodePtr, hc, and_self, ↓reduceIte]
  congr

/-- Every valid core type decodes from how it is written. -/
theorem Ty.decode_attr (t : Ty) (h : t.Valid) : Ty.decode t.attr = some t := by
  cases t with
  | ptr n =>
    have : n = 0 := h
    subst this
    rfl
  | float e m =>
    cases hn : floatAlias e m with
    | some n =>
      simp only [Ty.attr, hn]
      exact Ty.decode_alias (aliasFormat_of_floatAlias hn)
    | none =>
      simp only [Ty.attr, hn]
      exact Ty.decode_float hn h.2.2
  | int w =>
    have hne : "i" ++ toString w ≠ "ptr" := by
      intro he
      have := congrArg String.toList he
      simp at this
    simp only [Ty.attr]
    unfold Ty.decode
    split
    · rename_i he
      exact absurd (Attr.word.inj he) hne
    · rename_i he
      cases Attr.word.inj he
      simp only [toList_int_attr, ← Nat.repr_eq_ofList_toDigits, Nat.toNat?_repr, Option.bind_some]
      simp [toString, h.2]
    · rename_i he
      exact absurd he (by simp)
    · rename_i he
      exact absurd he (by simp)
    · rename_i _ _ hs _ _
      exact (hs _ rfl).elim

/-- A float type decodes only from how it is written. -/
theorem Ty.attr_decodeFloat {e m : Int} {t : Ty} (h : decodeFloat e m = some t) :
    t.attr = .app "float" [.int e, .int m] := by
  unfold decodeFloat at h
  split at h
  · rename_i hc
    cases h
    simp [Ty.attr, hc.2.2.2, Int.toNat_of_nonneg hc.1, Int.toNat_of_nonneg hc.2.1]
  · cases h

/-- A pointer type decodes only from how it is written. -/
theorem Ty.attr_decodePtr {n : Int} {t : Ty} (h : decodePtr n = some t) :
    t.attr = .app "ptr" [.int n] := by
  unfold decodePtr at h
  split at h
  · rename_i hc
    cases h
    obtain ⟨k, hk⟩ : ∃ k, n.toNat = k + 1 := ⟨n.toNat - 1, by omega⟩
    rw [hk]
    simp only [Ty.attr, Attr.app.injEq, List.cons.injEq, Attr.int.injEq, and_true, true_and]
    omega
  · cases h

/-- A core type decodes only from how it is written. -/
theorem Ty.attr_decode {a : Attr} {t : Ty} (h : Ty.decode a = some t) : t.attr = a := by
  unfold Ty.decode at h
  split at h
  · cases h
    rfl
  · rename_i s _
    split at h
    · rename_i ds hs
      obtain ⟨w, -, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · cases h
        rename_i hd
        have : s = "i" ++ String.ofList ds := by
          rw [← String.ofList_toList (s := s), hs]
          simp
        simp [Ty.attr, this, hd.1]
      · cases h
    · obtain ⟨⟨e, m⟩, he, rfl⟩ := Option.map_eq_some_iff.mp h
      simp [Ty.attr, floatAlias_of_aliasFormat he]
  · exact Ty.attr_decodeFloat h
  · exact Ty.attr_decodePtr h
  · cases h

/-! # Types as tokens -/

/-- Every valid core type is written as a type: `i` and its width form a
word, an alias is a word, `float(e, m)` applies a word to two integers,
`ptr` is a word and `ptr(N)` applies a word to an integer. -/
theorem Ty.attr_isType (t : Ty) (h : t.Valid) : t.attr.IsType := by
  cases t with
  | ptr n =>
    cases n with
    | zero => show isWord "ptr"; decide
    | succ k => exact ⟨by decide, trivial, trivial⟩
  | float e m =>
    cases hn : floatAlias e m with
    | some n =>
      simp only [Ty.attr, hn]
      unfold floatAlias at hn
      split at hn <;> cases hn <;> (show isWord _; decide)
    | none =>
      simp only [Ty.attr, hn]
      exact ⟨by decide, trivial, trivial, trivial⟩
  | int w =>
    show isWord ("i" ++ toString w)
    have hd : ∀ c ∈ Nat.toDigits 10 w, isNameChar c := fun c hc => by
      simp [isNameChar, Nat.isDigit_of_mem_toDigits (by omega) (by omega) hc]
    simp only [isWord, toList_int_attr, Bool.and_eq_true, List.all_eq_true]
    exact ⟨by decide, hd⟩

end Fir.Core
