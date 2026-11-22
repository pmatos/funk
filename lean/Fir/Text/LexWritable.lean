import Fir.Text.Tokens
import Fir.Text.SigAttrs

/-!
# Tokens that can be written

The tokens of attributes that can be written can be written, and so can
those of a list written with separators whose separator's and elements'
can. A function's parameters and results, each with its attributes, then
`...` when the parameters end in it, have tokens that can be written when
their definitions, types and attributes can.
-/

namespace Fir

open Text

/-- Splits a goal that every token of a list can be written into a goal for
each part of the list that is not punctuation. -/
local macro "split_writable" : tactic => `(tactic| (
  try simp only [List.forall_mem_cons, List.forall_mem_append, List.forall_mem_flatMap,
    List.not_mem_nil, false_implies, forall_const, Tok.Writable, and_true, true_and]
  try and_intros))

/-- Every token of a list written with separators can be written when the
separator's and each element's can. -/
theorem forall_mem_intercalate_of {P : Tok → Prop} {sep : List Tok} (hs : ∀ t ∈ sep, P t) :
    ∀ {tss : List (List Tok)}, (∀ ts ∈ tss, ∀ t ∈ ts, P t) → ∀ t ∈ sep.intercalate tss, P t
  | [], _ => by simp
  | [ts], h => by simpa using h ts (.head _)
  | ts :: ts' :: tss, h => by
    rw [List.intercalate_cons_cons]
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · rcases List.mem_append.mp ht with ht | ht
      · exact h ts (.head _) t ht
      · exact hs t ht
    · exact forall_mem_intercalate_of hs (fun us hus => h us (.tail _ hus)) t ht

theorem comma_writable : ∀ t ∈ [Tok.comma], t.Writable := by simp [Tok.Writable]

mutual
/-- The tokens of an attribute that can be written can be written. -/
theorem Attr.Writable.tokens : ∀ {a : Attr}, a.Writable → ∀ t ∈ a.tokens, t.Writable
  | .word _, h => fun t ht => by
    simp only [Attr.tokens, List.mem_singleton] at ht
    subst ht
    exact h
  | .int _, _ => by simp [Attr.tokens, Tok.Writable]
  | .str _, _ => by simp [Attr.tokens, Tok.Writable]
  | .sym _, _ => by simp [Attr.tokens, Tok.Writable]
  | .float _, h => by simpa [Attr.tokens, Tok.Writable, Attr.Writable] using h
  | .app _ args, h => by
    have hargs := Attr.AllWritable.tokens (as := args) h.2
    simp only [Attr.tokens]
    split_writable
    · exact h.1
    · exact forall_mem_intercalate_of comma_writable hargs

/-- The tokens of attributes that can be written can be written. -/
theorem Attr.AllWritable.tokens : ∀ {as : List Attr}, Attr.AllWritable as →
    ∀ ts ∈ Attr.tokens.tokensList as, ∀ t ∈ ts, t.Writable
  | [], _ => by simp [Attr.tokens.tokensList]
  | _ :: _, h => by
    simp only [Attr.tokens.tokensList, List.forall_mem_cons]
    exact ⟨Attr.Writable.tokens h.1, Attr.AllWritable.tokens h.2⟩
end

/-- Each attribute of a list that can be written can be written. -/
theorem Attr.AllWritable.mem : ∀ {as : List Attr}, Attr.AllWritable as → ∀ a ∈ as, a.Writable
  | [], _, _, ha => by simp at ha
  | _ :: _, h, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h.1
    · exact Attr.AllWritable.mem h.2 a ha

/-- A list whose attributes can each be written can be written. -/
theorem Attr.AllWritable.of_mem : ∀ {as : List Attr}, (∀ a ∈ as, a.Writable) → Attr.AllWritable as
  | [], _ => trivial
  | _ :: _, h => ⟨h _ (.head _), Attr.AllWritable.of_mem fun a ha => h a (.tail _ ha)⟩

/-- A type is an attribute that can be written. -/
theorem Attr.IsType.writable : ∀ {a : Attr}, a.IsType → a.Writable
  | .word _, h | .app .., h => h

variable {d : Dialect} [DialectText d]

/-- A function's parameters, each with its attributes, then `...` when they
end in it, have tokens that can be written when its definitions' and its
attributes' tokens can. -/
theorem Func.paramsTokens_writable (f : Func d)
    (hd : ∀ x ∈ f.params, ∀ t ∈ defTokens x, t.Writable)
    (ha : ∀ as ∈ f.paramAttrsAll, Attr.AllWritable as) : ∀ t ∈ f.paramsTokens, t.Writable := by
  unfold Func.paramsTokens
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · refine forall_mem_intercalate_of comma_writable (fun ts hts => ?_) t ht
    obtain ⟨⟨x, as⟩, hp, rfl⟩ := List.mem_map.mp hts
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact hd x (List.of_mem_zip hp).1 u hu
    · obtain ⟨a, hmem, hu⟩ := List.mem_flatMap.mp hu
      exact Attr.Writable.tokens ((ha as (List.of_mem_zip hp).2).mem a hmem) u hu
  · repeat' split at ht
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      try rcases ht with rfl | rfl
      all_goals first | (subst_vars; trivial) | trivial | simp at ht

/-- A function's results, each with its attributes, have tokens that can be
written when its result types are written as types and its attributes can
be written. -/
theorem Func.resultsTokens_writable (f : Func d) (ht : ∀ t ∈ f.results, (tyAttr t).IsType)
    (ha : ∀ as ∈ f.resultAttrsAll, Attr.AllWritable as) : ∀ t ∈ f.resultsTokens, t.Writable := by
  unfold Func.resultsTokens
  split
  · simp
  · refine List.forall_mem_cons.mpr ⟨trivial, forall_mem_intercalate_of comma_writable ?_⟩
    intro ts hts
    obtain ⟨⟨ty, as⟩, hp, rfl⟩ := List.mem_map.mp hts
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact Attr.Writable.tokens (ht ty (List.of_mem_zip hp).1).writable u hu
    · obtain ⟨a, hmem, hu⟩ := List.mem_flatMap.mp hu
      exact Attr.Writable.tokens ((ha as (List.of_mem_zip hp).2).mem a hmem) u hu

end Fir
