import Fir.Core.TypeTextLaws

/-!
`alloca` reads back from how it is written, and only from it, for every
instance, valid or not: its kind is one of three words, its type is written
as a type and reads back with no bound, its count is written only when it is
not 1, and its alignment as `align(A)` when it has one. Its attributes are
written as tokens. The laws of the core dialect's text use these facts.
-/

namespace Fir.Core

open Memory

/-- Every core type reads back, with no bound, from how it is written. -/
theorem Ty.decodeAny_attr (t : Ty) : Ty.decodeAny t.attr = some t := by
  cases t with
  | ptr n =>
    cases n with
    | zero => rfl
    | succ k =>
      have hc : (1 : Int) ≤ (k : Int) + 1 := by omega
      simp only [Ty.attr, Ty.decodeAny, hc, ↓reduceIte]
      congr
  | float e m =>
    cases hn : floatAlias e m with
    | some n =>
      simp only [Ty.attr, hn]
      have h := aliasFormat_of_floatAlias hn
      unfold aliasFormat at h
      split at h <;> cases h <;> rfl
    | none => simp [Ty.attr, hn, Ty.decodeAny]
  | int w =>
    have hne : "i" ++ toString w ≠ "ptr" := by
      intro he
      have := congrArg String.toList he
      simp at this
    simp only [Ty.attr]
    unfold Ty.decodeAny
    split
    · rename_i he
      exact absurd (Attr.word.inj he) hne
    · rename_i he
      cases Attr.word.inj he
      simp only [toList_int_attr, ← Nat.repr_eq_ofList_toDigits, Nat.toNat?_repr, Option.bind_some]
      simp [toString]
    · rename_i he
      exact absurd he (by simp)
    · rename_i he
      exact absurd he (by simp)
    · rename_i _ _ hs _ _
      exact (hs _ rfl).elim

/-- A core type reads back, with no bound, only from how it is written. -/
theorem Ty.attr_decodeAny {a : Attr} {t : Ty} (h : Ty.decodeAny a = some t) : t.attr = a := by
  unfold Ty.decodeAny at h
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
        simp [Ty.attr, this, hd]
      · cases h
    · obtain ⟨⟨e, m⟩, he, rfl⟩ := Option.map_eq_some_iff.mp h
      simp [Ty.attr, floatAlias_of_aliasFormat he]
  · split at h
    · rename_i hc
      cases h
      simp [Ty.attr, hc.2.2, Int.toNat_of_nonneg hc.1, Int.toNat_of_nonneg hc.2.1]
    · cases h
  · split at h
    · rename_i n hc
      cases h
      obtain ⟨k, hk⟩ : ∃ k, n.toNat = k + 1 := ⟨n.toNat - 1, by omega⟩
      rw [hk]
      simp only [Ty.attr, Attr.app.injEq, List.cons.injEq, Attr.int.injEq, and_true, true_and]
      omega
    · cases h
  · cases h

/-- The word of a kind is the only one that names it. -/
theorem word_of_decodeKind {w : String} {k : AllocKind} (h : decodeKind w = some k) :
    k.word = w := by
  unfold decodeKind at h
  split at h <;> cases h <;> rfl

/-- An alignment reads back from how it is written. -/
theorem decodeAlign_toList (a : Option Nat) :
    decodeAlign (a.toList.map fun (a : Nat) => .app "align" [.int a]) = some a := by
  cases a <;> simp [decodeAlign]

/-- An alignment reads back only from how it is written. -/
theorem toList_of_decodeAlign {as : List Attr} {a : Option Nat} (h : decodeAlign as = some a) :
    a.toList.map (fun (a : Nat) => Attr.app "align" [.int a]) = as := by
  unfold decodeAlign at h
  split at h
  · cases h
    rfl
  · split at h
    · rename_i hc
      cases h
      simp [Int.toNat_of_nonneg hc]
    · cases h
  · cases h

/-- Each `alloca` reads back from how it is written. -/
theorem decodeAlloca_allocaAttrs (k : AllocKind) (t : Ty) (c : Nat) (a : Option Nat) (n : Nat) :
    decodeAlloca (allocaAttrs k t c a) [] [.ptr n] = some (.alloca k t c a n) := by
  by_cases hc : c = 1
  · subst hc
    cases a <;> simp [allocaAttrs, decodeAlloca, decodeKind_word, Ty.decodeAny_attr, decodeAlign]
  · have hc' : (c : Int) ≠ 1 := by omega
    cases a <;> simp [allocaAttrs, decodeAlloca, decodeKind_word, Ty.decodeAny_attr, decodeAlign, hc,
      hc']

/-- `alloca` decodes only from its own name, its attributes, no operands and
a pointer result. -/
theorem decodeAlloca_eq {as : List Attr} {ts rs : List Ty} {op : Op}
    (h : decodeAlloca as ts rs = some op) :
    op.name = "alloca" ∧ op.attrs = as ∧ op.sig = ts ∧ op.returnTypes = rs := by
  unfold decodeAlloca at h
  split at h
  · split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨k, hk, t, ht, h⟩ := h
      split at h
      · split at h
        · rename_i c rest' hc
          obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
          have hc1 : c.toNat ≠ 1 := by omega
          refine ⟨rfl, ?_, rfl, rfl⟩
          simp [Op.attrs, allocaAttrs, word_of_decodeKind hk, Ty.attr_decodeAny ht, hc1,
            toList_of_decodeAlign ha, Int.toNat_of_nonneg hc.1]
        · cases h
      · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        refine ⟨rfl, ?_, rfl, rfl⟩
        simp [Op.attrs, allocaAttrs, word_of_decodeKind hk, Ty.attr_decodeAny ht,
          toList_of_decodeAlign ha]
    · cases h
  · cases h

/-- Every core type is written as tokens, valid or not. -/
theorem Ty.attr_writable (t : Ty) : t.attr.Writable := by
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

/-- `alloca`'s attributes are written as tokens. -/
theorem allocaAttrs_writable (k : AllocKind) (t : Ty) (c : Nat) (a : Option Nat) :
    Attr.AllWritable (allocaAttrs k t c a) := by
  have hk : isWord k.word := by cases k <;> decide
  by_cases hc : c = 1 <;> cases a <;>
    simp [allocaAttrs, hc, Attr.AllWritable, Attr.Writable, hk, Ty.attr_writable] <;> decide

end Fir.Core
