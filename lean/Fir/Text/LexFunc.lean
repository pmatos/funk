import Fir.Text.LexPrint

/-!
# Lexing a printed function's signature

A function's parameters are written each as its definition, then each of
its attributes after a space, separated by commas, then `...` when they
end in it, after a comma when a parameter comes before. Its results are
written after ` -> ` in the same way, each as its type and attributes. The
text of each part reads back as its tokens. An attribute after a type
starts with a space, so the type ends where it would end alone, and `...`
follows a `(` or a space, so no name character comes before it.
-/

namespace Fir

open Text

variable {d : Dialect} [DialectText d]

/-- A definition or a type, then its attributes, reads back as its
tokens. -/
theorem spells_withAttrs {s : String} {ts : List Tok} (h : Spells s.toList ts) (as : List Attr)
    (hw : ∀ t ∈ as.flatMap Attr.tokens, t.Writable) :
    Spells (s ++ printAttrs as).toList (ts ++ as.flatMap Attr.tokens) := by
  rw [String.toList_append]
  exact Spells.append h (spells_spaceAttrs as hw) (startsBoundary_spaceAttrs as)

/-- `...` reads back as its token. -/
theorem spells_ellipsis : Spells "...".toList [Tok.ellipsis] := Tok.spells (t := .ellipsis) trivial

/-- A function's parameters read back as their tokens. -/
theorem Func.spellsParams (f : Func d) (hw : ∀ t ∈ f.paramsTokens, t.Writable) :
    Spells f.printParams.toList f.paramsTokens := by
  unfold Func.printParams
  unfold Func.paramsTokens at hw ⊢
  have hall := forall_mem_intercalate (sep := [Tok.comma])
    (tss := (f.params.zip f.paramAttrsAll).map fun (x, as) =>
      defTokens x ++ as.flatMap Attr.tokens) fun t ht => hw t (List.mem_append_left _ ht)
  have heach : SpellsEach ((f.params.zip f.paramAttrsAll).map fun (x, as) =>
      printDef x ++ printAttrs as) ((f.params.zip f.paramAttrsAll).map fun (x, as) =>
      defTokens x ++ as.flatMap Attr.tokens) := SpellsEach.map fun p hp => by
    have hp' := hall _ (List.mem_map_of_mem hp)
    exact spells_withAttrs (spells_def p.1 fun t ht => hp' t (List.mem_append_left _ ht)) p.2
      fun t ht => hp' t (List.mem_append_right _ ht)
  have hsep := spells_commaSep heach
  rcases hv : f.variadic
  · simpa [hv] using hsep
  · rcases hp : f.params with _ | ⟨x, xs⟩
    · simpa [hv, hp] using spells_ellipsis
    · simp only [hp, List.isEmpty_cons, Bool.false_eq_true, ite_false, ite_true,
        String.toList_append, String.reduceToList] at hsep ⊢
      exact Spells.append hsep (Spells.comma (Spells.space spells_ellipsis))
        (startsBoundary_cons (by decide))

/-- A function's results read back as their tokens. -/
theorem Func.spellsResults (f : Func d) (hw : ∀ t ∈ f.resultsTokens, t.Writable) :
    Spells f.printResults.toList f.resultsTokens := by
  unfold Func.printResults
  unfold Func.resultsTokens at hw ⊢
  by_cases hr : f.results.isEmpty = true
  · simpa [hr] using Spells.nil
  · simp only [hr, Bool.false_eq_true, ite_false] at hw ⊢
    have hall := forall_mem_intercalate (sep := [Tok.comma])
      (tss := (f.results.zip f.resultAttrsAll).map fun (t, as) =>
        (tyAttr t).tokens ++ as.flatMap Attr.tokens) fun t ht => hw t (List.mem_cons_of_mem _ ht)
    have heach : SpellsEach ((f.results.zip f.resultAttrsAll).map fun (t, as) =>
        (tyAttr t).print ++ printAttrs as) ((f.results.zip f.resultAttrsAll).map fun (t, as) =>
        (tyAttr t).tokens ++ as.flatMap Attr.tokens) := SpellsEach.map fun p hp => by
      have hp' := hall _ (List.mem_map_of_mem hp)
      exact spells_withAttrs (Attr.spells _ fun t ht => hp' t (List.mem_append_left _ ht)) p.2
        fun t ht => hp' t (List.mem_append_right _ ht)
    intro cs us hs hl
    simp only [String.toList_append, String.reduceToList, List.cons_append, List.nil_append]
    exact Lexes.space <| Lexes.arrow <| Lexes.space <| spells_commaSep heach _ _ hs hl

end Fir
