import Fir.Text.LexPrint

/-!
# Lexing a printed module

The printer writes every op on a line of its own, and every block, region,
item and the location table end with a line feed or a `}`. So each of them
is read before whatever follows it (`SpellsAny`), and a module is read
piece by piece, from its first item to the end of its location table.

The result is `lex_print`: for every module whose tokens can be written,
the lexer reads its printed text as exactly `Module.tokens`, then `eof`,
positions aside. The grammar step of #11 starts from there: it reads
`Module.tokens`, at any positions, with `readModule`.
-/

namespace Fir

open Text

variable {d : Dialect} [DialectText d]

/-- An op's results and its `=`, when it has results. -/
theorem spells_lhs (results : List (Name × d.Ty))
    (hw : ∀ t ∈ (if results.isEmpty = true then [] else defsTokens results ++ [Tok.eq]), t.Writable) :
    SpellsAny (if results.isEmpty = true then "" else printDefs results ++ " = ").toList
      (if results.isEmpty = true then [] else defsTokens results ++ [Tok.eq]) := by
  by_cases hr : results.isEmpty = true
  · simp only [hr, ite_true, String.reduceToList]
    exact SpellsAny.nil
  · simp only [hr, Bool.false_eq_true, ite_false] at hw ⊢
    simp only [String.toList_append, String.reduceToList]
    exact Spells.append_any (spells_defs results fun t ht => hw t (by simp [ht]))
      (SpellsAny.space (SpellsAny.eq (SpellsAny.space SpellsAny.nil))) fun _ => boundary_space _

/-- An op's name, attributes, operands and successors. -/
theorem spells_rhs (op : d.Op) (operands : List Name) (succs : List Succ)
    (hw : ∀ t ∈ (if (operands.map ([Tok.value ·]) ++ succs.map Succ.tokens).isEmpty = true then
        Tok.word (opName op) :: (opAttrs op).flatMap Attr.tokens
      else Tok.word (opName op) :: (opAttrs op).flatMap Attr.tokens ++
        [Tok.comma].intercalate (operands.map ([Tok.value ·]) ++ succs.map Succ.tokens)), t.Writable) :
    Spells (if (operands.map ("%" ++ ·) ++ succs.map Succ.print).isEmpty = true then
        " ".intercalate (opName op :: (opAttrs op).map Attr.print)
      else " ".intercalate (opName op :: (opAttrs op).map Attr.print) ++ " " ++
        ", ".intercalate (operands.map ("%" ++ ·) ++ succs.map Succ.print)).toList
      (if (operands.map ([Tok.value ·]) ++ succs.map Succ.tokens).isEmpty = true then
        Tok.word (opName op) :: (opAttrs op).flatMap Attr.tokens
      else Tok.word (opName op) :: (opAttrs op).flatMap Attr.tokens ++
        [Tok.comma].intercalate (operands.map ([Tok.value ·]) ++ succs.map Succ.tokens)) := by
  have hhead_w : ∀ t ∈ Tok.word (opName op) :: (opAttrs op).flatMap Attr.tokens, t.Writable :=
    fun t ht => hw t (by split; exact ht; exact List.mem_append_left _ ht)
  have hop : isWord (opName op) = true := hhead_w (.word (opName op)) (.head _)
  have heach : SpellsEach (opName op :: (opAttrs op).map Attr.print)
      ([Tok.word (opName op)] :: (opAttrs op).map Attr.tokens) :=
    ⟨spells_word hop, SpellsEach.map fun a ha => Attr.spells a fun t ht =>
      hhead_w t (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨a, ha, ht⟩))⟩
  have hhead : Spells (" ".intercalate (opName op :: (opAttrs op).map Attr.print)).toList
      (Tok.word (opName op) :: (opAttrs op).flatMap Attr.tokens) := spells_spaceSep heach
  by_cases hu : operands = [] ∧ succs = []
  · obtain ⟨rfl, rfl⟩ := hu
    simpa using hhead
  · have hne : (operands.map ("%" ++ ·) ++ succs.map Succ.print).isEmpty = false := by
      cases operands <;> cases succs <;> simp_all
    have hne' : (operands.map ([Tok.value ·]) ++ succs.map Succ.tokens).isEmpty = false := by
      cases operands <;> cases succs <;> simp_all
    simp only [hne, hne', Bool.false_eq_true, ite_false] at hw ⊢
    have hall := forall_mem_intercalate (sep := [Tok.comma])
      (tss := operands.map ([Tok.value ·]) ++ succs.map Succ.tokens) fun t ht =>
        hw t (List.mem_append_right _ ht)
    have huses : SpellsEach (operands.map ("%" ++ ·) ++ succs.map Succ.print)
        (operands.map ([Tok.value ·]) ++ succs.map Succ.tokens) :=
      SpellsEach.append
        (SpellsEach.map fun x hx => spells_use (hall [Tok.value x]
          (List.mem_append_left _ (List.mem_map_of_mem (f := ([Tok.value ·])) hx)) _ (.head _)))
        (SpellsEach.map fun s hs => Succ.spells s (hall _
          (List.mem_append_right _ (List.mem_map_of_mem (f := Succ.tokens) hs))))
    simp only [String.toList_append, String.reduceToList, List.append_assoc, List.cons_append,
      List.nil_append]
    exact Spells.append hhead (Spells.space (spells_commaSep huses)) (startsBoundary_cons (by decide))

/-- What follows an op's last attribute, operand or successor: its regions,
then a space. -/
theorem boundary_regions (n : Nat) (rs : List (Region d)) (cs : List Char) :
    Boundary ((Region.printList n rs).toList ++ ' ' :: cs) := by
  cases rs with
  | nil => exact boundary_space _
  | cons r rs =>
    cases r
    simp only [Region.printList, String.toList_append, String.reduceToList, List.cons_append,
      List.append_assoc]
    exact boundary_space _

mutual
/-- An op reads back as its tokens, before any text. -/
theorem Operation.spells (n : Nat) : ∀ o : Operation d, (∀ t ∈ o.tokens, t.Writable) →
    SpellsAny (o.print n).toList o.tokens
  | ⟨results, op, operands, succs, regions, loc⟩, hw => by
    simp only [Operation.tokens] at hw
    have hloc : loc < Location.limit :=
      hw (.locRef loc) (List.mem_append_right _ (List.mem_singleton_self _))
    have hreg := Region.spellsList n regions fun t ht =>
      hw t (List.mem_append_left _ (List.mem_append_right _ ht))
    have hlhs := spells_lhs results fun t ht =>
      hw t (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ht)))
    have hrhs := spells_rhs op operands succs fun t ht =>
      hw t (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ht)))
    simp only [Operation.print, Operation.tokens, String.toList_append, String.reduceToList,
      List.append_assoc, List.cons_append, List.nil_append]
    exact SpellsAny.indent (SpellsAny.append_any hlhs (Spells.append_any hrhs
      (SpellsAny.append_any hreg (SpellsAny.space (Spells.tok_any (t := .locRef loc) hloc
        (SpellsAny.lf SpellsAny.nil) fun _ => boundary_cons (by decide))))
      fun cs => by simpa using boundary_regions n regions _)) n

/-- The regions of an op read back as their tokens, before any text. -/
theorem Region.spellsList (n : Nat) : ∀ rs : List (Region d), (∀ t ∈ Region.tokensList rs, t.Writable) →
    SpellsAny (Region.printList n rs).toList (Region.tokensList rs)
  | [], _ => by simpa [Region.printList, Region.tokensList] using SpellsAny.nil
  | ⟨blocks⟩ :: rs, hw => by
    have hb := Block.spellsList (n + 2) blocks fun t ht => hw t (by simp [Region.tokensList, ht])
    have hr := Region.spellsList n rs fun t ht => hw t (by simp [Region.tokensList, ht])
    simp only [Region.printList, Region.tokensList, String.toList_append, String.reduceToList,
      List.append_assoc, List.cons_append, List.nil_append]
    exact SpellsAny.space (SpellsAny.lbrace (SpellsAny.lf (SpellsAny.append_any hb
      (SpellsAny.indent (SpellsAny.rbrace hr) n))))

/-- Blocks read back as their tokens, before any text. -/
theorem Block.spellsList (n : Nat) : ∀ bs : List (Block d), (∀ t ∈ Block.tokensList bs, t.Writable) →
    SpellsAny (Block.printList n bs).toList (Block.tokensList bs)
  | [], _ => by simpa [Block.printList, Block.tokensList] using SpellsAny.nil
  | ⟨label, params, body⟩ :: bs, hw => by
    have hlab : isName label = true := hw (.label label) (by simp [Block.tokensList])
    have hops := Operation.spellsList (n + 2) body fun t ht => hw t (by simp [Block.tokensList, ht])
    have hbs := Block.spellsList n bs fun t ht => hw t (by simp [Block.tokensList, ht])
    have hlabel : ∀ {s ts}, SpellsAny s ts → (∀ cs, Boundary (s ++ cs)) →
        SpellsAny ('^' :: (label.toList ++ s)) (.label label :: ts) := fun h hs cs us hl => by
      simpa using Lexes.label hlab (hs cs) (h cs us hl)
    by_cases hp : params.isEmpty = true
    · simp only [Block.printList, Block.tokensList, hp, ite_true, String.toList_append,
        String.reduceToList, List.append_assoc, List.cons_append, List.nil_append]
      exact SpellsAny.indent (hlabel (SpellsAny.colon (SpellsAny.lf (SpellsAny.append_any hops hbs)))
        fun _ => boundary_cons (by decide)) n
    · have hdefs := spells_defs params fun t ht => hw t (by simp [Block.tokensList, hp, ht])
      simp only [Block.printList, Block.tokensList, hp, Bool.false_eq_true, ite_false,
        String.toList_append, String.reduceToList, List.append_assoc, List.cons_append,
        List.nil_append]
      exact SpellsAny.indent (hlabel (SpellsAny.lparen (Spells.append_any hdefs
        (SpellsAny.rparen (SpellsAny.colon (SpellsAny.lf (SpellsAny.append_any hops hbs))))
        fun _ => boundary_cons (by decide))) fun _ => boundary_cons (by decide)) n

/-- Ops read back as their tokens, before any text. -/
theorem Operation.spellsList (n : Nat) : ∀ os : List (Operation d),
    (∀ t ∈ Operation.tokensList os, t.Writable) →
    SpellsAny (Operation.printList n os).toList (Operation.tokensList os)
  | [], _ => by simpa [Operation.printList, Operation.tokensList] using SpellsAny.nil
  | o :: os, hw => by
    simp only [Operation.printList, Operation.tokensList, String.toList_append]
    exact SpellsAny.append_any
      (Operation.spells n o fun t ht => hw t (by simp [Operation.tokensList, ht]))
      (Operation.spellsList n os fun t ht => hw t (by simp [Operation.tokensList, ht]))
end

/-- A function reads back as its tokens, before any text. -/
theorem Func.spells (f : Func d) (hw : ∀ t ∈ f.tokens, t.Writable) :
    SpellsAny f.print.toList f.tokens := by
  have hdefs := spells_defs f.params fun t ht => hw t (by simp [Func.tokens, ht])
  have hblocks := Block.spellsList 0 f.body.blocks fun t ht => hw t (by simp [Func.tokens, ht])
  intro cs us hl
  by_cases hr : f.results.isEmpty = true
  · simp only [Func.print, Func.tokens, hr, ite_true, String.toList_append, String.reduceToList,
      List.append_assoc, List.cons_append, List.nil_append]
    exact Lexes.lit "func" ['f', 'u', 'n', 'c'] (boundary_space _) <| Lexes.space <|
      Lexes.sym _ (boundary_cons (by decide)) <| Lexes.lparen <|
      hdefs _ _ (boundary_cons (by decide)) <| Lexes.rparen <| Lexes.space <| Lexes.lbrace <|
      Lexes.lf <| hblocks _ _ <| Lexes.rbrace <| Lexes.lf hl
  · simp only [Func.tokens, hr, Bool.false_eq_true, ite_false] at hw
    have hall := forall_mem_intercalate (sep := [Tok.comma])
      (tss := f.results.map (tyAttr · |>.tokens)) fun t ht => hw t (by simp [ht])
    have htypes : SpellsEach (f.results.map (tyAttr · |>.print)) (f.results.map (tyAttr · |>.tokens)) :=
      SpellsEach.map fun ty hty =>
        Attr.spells _ (hall _ (List.mem_map_of_mem (f := (tyAttr · |>.tokens)) hty))
    simp only [Func.print, Func.tokens, hr, Bool.false_eq_true, ite_false, String.toList_append,
      String.reduceToList, List.append_assoc, List.cons_append, List.nil_append]
    exact Lexes.lit "func" ['f', 'u', 'n', 'c'] (boundary_space _) <| Lexes.space <|
      Lexes.sym _ (boundary_cons (by decide)) <| Lexes.lparen <|
      hdefs _ _ (boundary_cons (by decide)) <| Lexes.rparen <| Lexes.space <| Lexes.arrow <|
      Lexes.space <| spells_commaSep htypes _ _ (boundary_space _) <| Lexes.space <| Lexes.lbrace <|
      Lexes.lf <| hblocks _ _ <| Lexes.rbrace <| Lexes.lf hl

/-- An item reads back as its tokens, before any text. -/
theorem Item.spells : ∀ i : Item d, (∀ t ∈ i.tokens, t.Writable) → SpellsAny i.print.toList i.tokens
  | .func f, hw => Func.spells f hw

/-- The entries of the location table read back as their tokens. -/
theorem LocTable.spellsEntries (t : LocTable)
    (hw : ∀ x ∈ t.flatMap (fun (r, l) => .locRef r :: .eq :: l.tokens), x.Writable) :
    SpellsAny
      (String.join (t.map fun (r, l) => "  " ++ printLocRef r ++ " = " ++ l.print ++ "\n")).toList
      (t.flatMap fun (r, l) => .locRef r :: .eq :: l.tokens) := by
  induction t with
  | nil => simpa using SpellsAny.nil
  | cons e t ih =>
    obtain ⟨r, l⟩ := e
    have hr : r < Location.limit := hw (.locRef r) (by simp)
    have hl' : ∀ x ∈ l.tokens, x.Writable := fun x hx => hw x (by simp [hx])
    have ih := ih fun x hx => hw x (List.mem_append_right _ hx)
    intro cs us hl
    simp only [List.map_cons, String.join_cons, List.flatMap_cons, String.toList_append,
      String.reduceToList, List.append_assoc, List.cons_append, List.nil_append]
    exact Lexes.space <| Lexes.space <| Lexes.locRef hr (boundary_space _) <| Lexes.space <|
      Lexes.eq <| Lexes.space <| Location.spells l hl' _ _ (boundary_cons (by decide)) <|
      Lexes.lf <| ih cs us hl

/-- The location table reads back as its tokens, before any text. -/
theorem LocTable.spells (t : LocTable) (hw : ∀ x ∈ t.tokens, x.Writable) :
    SpellsAny t.print.toList t.tokens := by
  have he := LocTable.spellsEntries t fun x hx => hw x (by simp [LocTable.tokens, hx])
  intro cs us hl
  simp only [LocTable.print, LocTable.tokens, String.toList_append, String.reduceToList,
    List.append_assoc, List.cons_append, List.nil_append]
  exact Lexes.lit "locs" ['l', 'o', 'c', 's'] (boundary_space _) <| Lexes.space <| Lexes.lbrace <|
    Lexes.lf <| he _ _ <| Lexes.rbrace <| Lexes.lf hl

/-- Items, each followed by an empty line, read back as their tokens. -/
theorem Module.spellsItems (items : List (Item d)) (hw : ∀ t ∈ items.flatMap Item.tokens, t.Writable) :
    SpellsAny (String.join (items.map (·.print ++ "\n"))).toList (items.flatMap Item.tokens) := by
  induction items with
  | nil => simpa using SpellsAny.nil
  | cons i is ih =>
    have hi := Item.spells i fun t ht => hw t (List.mem_append_left _ ht)
    have ih := ih fun t ht => hw t (List.mem_append_right _ ht)
    simp only [List.map_cons, String.join_cons, List.flatMap_cons, String.toList_append,
      String.reduceToList, List.append_assoc, List.cons_append, List.nil_append]
    exact SpellsAny.append_any hi (SpellsAny.lf ih)

/-- A module reads back as its tokens, before any text. -/
theorem Module.spells (m : Module d) (hw : ∀ t ∈ m.tokens, t.Writable) :
    SpellsAny m.print.toList m.tokens := by
  simp only [Module.print, Module.tokens, String.toList_append]
  exact SpellsAny.append_any (Module.spellsItems m.items fun t ht => hw t (List.mem_append_left _ ht))
    (LocTable.spells m.locs fun t ht => hw t (List.mem_append_right _ ht))

/-- Lexing printed text: for every module whose tokens can be written, the
lexer reads its printed text as exactly its tokens, then `eof`. The
positions are the lexer's own; the grammar step reads the tokens at any
positions. -/
theorem lex_print {m : Module d} (hw : ∀ t ∈ m.tokens, t.Writable) :
    ∃ ts, lex m.print = .ok ts ∧ ts.map (·.tok) = m.tokens ++ [.eof] := by
  obtain ⟨r, h₁, h₂⟩ := Module.spells m hw [] [] Lexes.nil ⟨1, 1⟩ []
  rw [List.append_nil] at h₁
  exact ⟨r, by simpa [lex] using h₁, by simpa using h₂⟩

end Fir
