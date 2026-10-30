import Fir.Text.LexLayout

/-!
# Reading printed attributes, locations and definitions

Each printer function below writes the tokens of the matching token
function, in its one layout: `Attr.print` writes `Attr.tokens`,
`Location.print` writes `Location.tokens`, and so on. Each lemma assumes
only that the tokens can be written, and reads the text one piece at a
time, as the printer writes it.
-/

namespace Fir

open Text

theorem toString_string (s : String) : toString s = s := rfl

mutual
/-- An attribute, or a type, reads back as its tokens. -/
theorem Attr.spells : ∀ a : Attr, (∀ t ∈ a.tokens, t.Writable) → Spells a.print.toList a.tokens
  | .word w, hw => Tok.spells (t := .word w) (hw _ (by simp [Attr.tokens]))
  | .int i, _ => Tok.spells (t := .int i) trivial
  | .str s, _ => Tok.spells (t := .str s) trivial
  | .sym s, _ => Tok.spells (t := .sym s) trivial
  | .app h args, hw => by
    have hh : isWord h = true := hw (.word h) (by simp [Attr.tokens])
    have heach := Attr.spellsEach args <| forall_mem_intercalate (sep := [Tok.comma])
      (tss := Attr.tokens.tokensList args) fun t ht => hw t (by simp [Attr.tokens, ht])
    intro cs us hs hl
    simp only [Attr.print, Attr.tokens, String.toList_append, String.reduceToList, List.append_assoc,
      List.cons_append, List.nil_append]
    exact Lexes.word hh (boundary_cons (by decide)) <| Lexes.lparen <|
      spells_commaSep heach _ _ (boundary_cons (by decide)) <| Lexes.rparen hl

/-- The attributes of a list read back as their tokens, one by one. -/
theorem Attr.spellsEach : ∀ as : List Attr, (∀ ts ∈ Attr.tokens.tokensList as, ∀ t ∈ ts, t.Writable) →
    SpellsEach (Attr.print.printList as) (Attr.tokens.tokensList as)
  | [], _ => trivial
  | a :: as, hw =>
    ⟨Attr.spells a (hw _ (.head _)), Attr.spellsEach as fun ts hts => hw ts (.tail _ hts)⟩
end

/-- A location reads back as its tokens. -/
theorem Location.spells (l : Location) (hw : ∀ t ∈ l.tokens, t.Writable) :
    Spells l.print.toList l.tokens := by
  intro cs us hs hl
  cases l with
  | unknown =>
    simp only [Location.print, Location.tokens, String.reduceToList, List.cons_append, List.nil_append]
    exact Lexes.lit "unknown" ['u', 'n', 'k', 'n', 'o', 'w', 'n'] hs hl
  | range f l₁ c₁ l₂ c₂ =>
    simp only [Location.print, Location.tokens, String.toList_append, String.reduceToList,
      List.append_assoc, List.cons_append, List.nil_append, toString_string]
    exact Lexes.quote f (boundary_cons (by decide)) <| Lexes.colon <|
      Lexes.nat l₁ (boundary_cons (by decide)) <| Lexes.colon <| Lexes.nat c₁ (boundary_space _) <|
      Lexes.space <| Lexes.lit "to" ['t', 'o'] (boundary_space _) <| Lexes.space <|
      Lexes.nat l₂ (boundary_cons (by decide)) <| Lexes.colon <| Lexes.nat c₂ hs hl
  | name n =>
    simp only [Location.print, Location.tokens, String.toList_append, String.reduceToList,
      List.append_assoc, List.cons_append, List.nil_append, toString_string]
    exact Lexes.lit "name" ['n', 'a', 'm', 'e'] (boundary_cons (by decide)) <| Lexes.lparen <|
      Lexes.quote n (boundary_cons (by decide)) <| Lexes.rparen hl
  | callsite callee caller =>
    have h₁ : callee < Location.limit := hw (.locRef callee) (by simp [Location.tokens])
    have h₂ : caller < Location.limit := hw (.locRef caller) (by simp [Location.tokens])
    simp only [Location.print, Location.tokens, String.toList_append, String.reduceToList,
      List.append_assoc, List.cons_append, List.nil_append, toString_string]
    exact Lexes.lit "callsite" ['c', 'a', 'l', 'l', 's', 'i', 't', 'e'] (boundary_cons (by decide)) <|
      Lexes.lparen <| Lexes.locRef h₁ (boundary_space _) <| Lexes.space <|
      Lexes.lit "at" ['a', 't'] (boundary_space _) <| Lexes.space <|
      Lexes.locRef h₂ (boundary_cons (by decide)) <| Lexes.rparen hl
  | fused locs =>
    have hall := forall_mem_intercalate (sep := [Tok.comma])
      (tss := locs.map ([Tok.locRef ·])) fun t ht => hw t (by simp [Location.tokens, ht])
    have heach : SpellsEach (locs.map printLocRef) (locs.map ([Tok.locRef ·])) :=
      SpellsEach.map fun r hr => Tok.spells (t := .locRef r)
        (hall _ (List.mem_map_of_mem hr) _ (.head _))
    simp only [Location.print, Location.tokens, String.toList_append, String.reduceToList,
      List.append_assoc, List.cons_append, List.nil_append]
    exact Lexes.lit "fused" ['f', 'u', 's', 'e', 'd'] (boundary_cons (by decide)) <| Lexes.lparen <|
      spells_commaSep heach _ _ (boundary_cons (by decide)) <| Lexes.rparen hl
  | derived src =>
    have h₁ : src < Location.limit := hw (.locRef src) (by simp [Location.tokens])
    simp only [Location.print, Location.tokens, String.toList_append, String.reduceToList,
      List.append_assoc, List.cons_append, List.nil_append, toString_string]
    exact Lexes.lit "derived" ['d', 'e', 'r', 'i', 'v', 'e', 'd'] (boundary_cons (by decide)) <|
      Lexes.lparen <| Lexes.locRef h₁ (boundary_cons (by decide)) <| Lexes.rparen hl

variable {d : Dialect} [DialectText d]

/-- A definition reads back as its tokens. -/
theorem spells_def (x : Name × d.Ty) (hw : ∀ t ∈ defTokens x, t.Writable) :
    Spells (printDef x).toList (defTokens x) := by
  have h₁ : isName x.1 = true := hw (.value x.1) (by simp [defTokens])
  have h₂ : ∀ t ∈ (tyAttr x.2).tokens, t.Writable := fun t ht => hw t (by simp [defTokens, ht])
  intro cs us hs hl
  simp only [printDef, defTokens, String.toList_append, String.reduceToList, List.append_assoc,
    List.cons_append, List.nil_append]
  exact Lexes.value h₁ (boundary_cons (by decide)) <| Lexes.colon <| Lexes.space <|
    Attr.spells _ h₂ _ _ hs hl

/-- Definitions read back as their tokens. -/
theorem spells_defs (xs : List (Name × d.Ty)) (hw : ∀ t ∈ defsTokens xs, t.Writable) :
    Spells (printDefs xs).toList (defsTokens xs) :=
  spells_commaSep <| SpellsEach.map fun x hx =>
    spells_def x (forall_mem_intercalate hw _ (List.mem_map_of_mem hx))

/-- A use of a value, `%x`. -/
theorem spells_use {x : Name} (hx : isName x = true) : Spells ("%" ++ x).toList [.value x] :=
  Tok.spells (t := .value x) hx

/-- A successor reads back as its tokens. -/
theorem Succ.spells (s : Succ) (hw : ∀ t ∈ s.tokens, t.Writable) : Spells s.print.toList s.tokens := by
  intro cs us hs hl
  by_cases he : s.args.isEmpty
  · have h₁ : isName s.label = true := hw (.label s.label) (by simp [Succ.tokens])
    simp only [Succ.print, Succ.tokens, he, ite_true, String.toList_append, String.reduceToList,
      List.append_assoc, List.cons_append, List.nil_append]
    exact Lexes.label h₁ hs hl
  · have h₁ : isName s.label = true := hw (.label s.label) (by simp [Succ.tokens])
    have hall := forall_mem_intercalate (sep := [Tok.comma])
      (tss := s.args.map ([Tok.value ·])) fun t ht => hw t (by simp [Succ.tokens, he, ht])
    have heach : SpellsEach (s.args.map ("%" ++ ·)) (s.args.map ([Tok.value ·])) :=
      SpellsEach.map fun x hx => spells_use (hall _ (List.mem_map_of_mem hx) _ (.head _))
    simp only [Succ.print, Succ.tokens, he, Bool.false_eq_true, ite_false, String.toList_append,
      String.reduceToList, List.append_assoc, List.cons_append, List.nil_append]
    exact Lexes.label h₁ (boundary_cons (by decide)) <| Lexes.lparen <|
      spells_commaSep heach _ _ (boundary_cons (by decide)) <| Lexes.rparen hl

end Fir
