import Fir.Text.ReadAttrs

/-!
# Reading definitions, operands and successors

A definition's tokens, `%x: T`, read back as the definition's tree, before
any token but `(`: a type that is a word would be applied by a `(` after
it. A list of definitions reads back before any token but `(` and a comma.
An op's operands and successors read back before its regions or its
location reference, whichever comes first: `{` or `@N`.
-/

namespace Fir.Text

/-- Takes the first token off `h : ts.map (·.tok) = t :: rest`: `ts` becomes
`⟨t, p⟩ :: ts'`, and `h` says that `ts'.map (·.tok) = rest`. -/
local macro "take_tok " h:ident : tactic => `(tactic| (
  (try dsimp only at $h:ident)
  replace $h:ident := map_tok_cons $h
  obtain ⟨_, _, he, $h:ident⟩ := $h
  subst he))

/-- `take_tok`, naming the token's position `p`. -/
local macro "take_pos " h:ident p:ident : tactic => `(tactic| (
  (try dsimp only at $h:ident)
  replace $h:ident := map_tok_cons $h
  obtain ⟨$p:ident, _, he, $h:ident⟩ := $h
  subst he))

variable {d : Dialect} [DialectText d]

/-- `readDefType` reads the `:` and the type of a definition of `x`. -/
theorem readDefType_reads (p : TextPos) {x : Name × d.Ty} (hx : (tyAttr x.2).IsType) :
    Reads (readDefType x.1 p) SDef.erase (defTree x) (.colon :: (tyAttr x.2).tokens)
      (· ≠ .lparen) := by
  intro ts rest h hs
  simp only [List.cons_append] at h
  take_tok h
  obtain ⟨⟨ty, tp⟩, ⟨r, hr⟩, h₁, h₂, h₃⟩ := readType_reads hx _ rest h hs
  simp only [readDefType, expect_cons, ok_bind, h₁]
  refine ⟨_, _, rfl, ?_, h₃⟩
  simp only [eraseAt, Prod.mk.injEq] at h₂
  simp [SDef.erase, defTree, h₂.1]

/-- `readDef` reads a definition's tokens as its tree. -/
theorem readDef_reads {x : Name × d.Ty} (hx : (tyAttr x.2).IsType) :
    Reads readDef SDef.erase (defTree x) (defTokens x) (· ≠ .lparen) := by
  intro ts rest h hs
  simp only [defTokens, List.cons_append] at h
  take_pos h p
  obtain ⟨sd, ⟨r, hr⟩, h₁, h₂, h₃⟩ := readDefType_reads p hx _ rest h hs
  rw [readDef.eq_1]
  simp only [h₁, ok_bind]
  exact ⟨_, _, rfl, h₂, h₃⟩

/-- Elements written with a comma before each, from their tokens. -/
theorem flatMap_comma_map {γ : Type} (xs : List γ) (toks : γ → List Tok) :
    (xs.map toks).flatMap (.comma :: ·) = xs.flatMap (.comma :: toks ·) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- `readDefs` reads the tokens of one or more definitions as their trees,
before any token but `(` and a comma. -/
theorem readDefs_reads {xs : List (Name × d.Ty)} (hne : xs ≠ [])
    (hx : ∀ x ∈ xs, (tyAttr x.2).IsType) :
    Reads readDefs (List.map SDef.erase) (xs.map defTree) (defsTokens xs)
      (fun t => t ≠ .lparen ∧ t ≠ .comma) := by
  intro ts rest h hs
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [defsTokens, List.map_cons, intercalate_cons, List.append_assoc, flatMap_comma_map] at h
  obtain ⟨sd, ⟨r, hr⟩, h₁, h₂, h₃⟩ := readDef_reads (hx x (.head _)) ts
    (xs.flatMap (.comma :: defTokens ·) ++ rest) h
    (head?_append _ (by cases xs <;> simp) fun t ht => (hs t ht).1)
  obtain ⟨sds, ⟨r', hr'⟩, h₄, h₅, h₆⟩ := Reads.more (stop := (· ≠ .lparen)) (by decide)
    (fun t ht => ht) (fun y hy => readDef_reads (hx y (.tail _ hy))) r rest h₃ hs
  simp only [readDefs, h₁, ok_bind, h₄]
  exact ⟨_, _, rfl, by simp [h₂, h₅], h₆⟩

/-- `readSuccArgs` reads the values a successor passes, then `)`. -/
theorem readSuccArgs_reads : ∀ {args : List Name}, args ≠ [] →
    Reads readSuccArgs id args ([Tok.comma].intercalate (args.map ([.value ·])) ++ [.rparen])
      (fun _ => True)
  | [], hne, _, _, _, _ => absurd rfl hne
  | [v], _, ts, rest, h, _ => by
    simp only [List.map_cons, List.map_nil, List.intercalate_singleton, List.cons_append,
      List.nil_append] at h
    take_tok h
    rw [readSuccArgs.eq_2 _ _ _ (not_cons_of_head h (by simp))]
    take_tok h
    simp only [expect_cons, ok_bind]
    exact ⟨_, _, rfl, rfl, h⟩
  | v :: v' :: vs, _, ts, rest, h, _ => by
    rw [List.map_cons, List.map_cons, List.intercalate_cons_cons] at h
    simp only [List.cons_append, List.nil_append, List.append_assoc] at h
    take_tok h
    take_tok h
    obtain ⟨vs', ⟨r, hr⟩, h₁, h₂, h₃⟩ := readSuccArgs_reads (args := v' :: vs)
      (List.cons_ne_nil _ _) _ rest (by simpa using h) fun _ _ => trivial
    rw [readSuccArgs.eq_1]
    simp only [h₁, ok_bind]
    exact ⟨_, _, rfl, by simp [← h₂], h₃⟩

/-- `readSucc` reads a successor's tokens as the successor, before any
token but `(`. -/
theorem Succ.reads (s : Succ) : Reads readSucc id s s.tokens (· ≠ .lparen) := by
  intro ts rest h hs
  obtain ⟨l, args⟩ := s
  cases args with
  | nil =>
    simp only [Succ.tokens, List.isEmpty_nil, ↓reduceIte, List.cons_append, List.nil_append] at h
    take_tok h
    rw [readSucc.eq_2 _ _ _ (not_cons_of_head h hs)]
    exact ⟨_, _, rfl, rfl, h⟩
  | cons a as =>
    simp only [Succ.tokens, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.cons_append,
      List.append_assoc] at h
    take_tok h
    take_tok h
    obtain ⟨args, ⟨r, hr⟩, h₁, h₂, h₃⟩ := readSuccArgs_reads (List.cons_ne_nil a as) _ rest
      (by simpa using h) fun _ _ => trivial
    rw [readSucc.eq_1]
    simp only [h₁, ok_bind]
    exact ⟨_, _, rfl, by simp [← h₂], h₃⟩

/-- What follows an op's operands and successors: a region or its location
reference. -/
def EndsUses (t : Tok) : Prop := t = .lbrace ∨ ∃ r, t = .locRef r

/-- After an op's uses there is no comma and no `(`. -/
theorem EndsUses.ne {t : Tok} (h : EndsUses t) : t ≠ .comma ∧ t ≠ .lparen := by
  rcases h with rfl | ⟨r, rfl⟩ <;> simp

/-- The successors that follow an op's operands, each after a comma. -/
theorem readMore_succs (succs : List Succ) :
    Reads (readMore readSucc) (List.map id) (succs.map id) (succs.flatMap (.comma :: Succ.tokens ·))
      EndsUses :=
  Reads.more (stop := (· ≠ .lparen)) (by decide) (fun _ ht => ⟨ht.ne.2, ht.ne.1⟩)
    fun s _ => Succ.reads s

/-- `readMoreOperands` reads `, %x` for each operand after the first, then
the successors, each after a comma. -/
theorem readMoreOperands_reads (succs : List Succ) : ∀ vs : List Name,
    Reads readMoreOperands (fun r => (r.1.map eraseAt, r.2)) (vs.map (·, TextPos.zero), succs)
      (vs.flatMap (fun v => [.comma, .value v]) ++ succs.flatMap (.comma :: Succ.tokens ·))
      EndsUses
  | [], ts, rest, h, hs => by
    simp only [List.flatMap_nil, List.nil_append] at h
    have hne : ∀ pos v p rest', ts = ⟨.comma, pos⟩ :: ⟨.value v, p⟩ :: rest' → False := by
      intro pos v p rest' he
      subst he
      cases succs with
      | nil =>
        simp only [List.flatMap_nil, List.nil_append] at h
        exact (hs .comma (by rw [← h]; rfl)).ne.1 rfl
      | cons s ss => simp [Succ.tokens] at h
    obtain ⟨ss, ⟨r, hr⟩, h₁, h₂, h₃⟩ := readMore_succs succs ts rest h hs
    rw [readMoreOperands.eq_2 _ hne]
    simp only [h₁, ok_bind]
    exact ⟨_, _, rfl, by simpa using h₂, h₃⟩
  | v :: vs, ts, rest, h, hs => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc] at h
    take_tok h
    take_tok h
    obtain ⟨⟨vs', ss⟩, ⟨r, hr⟩, h₁, h₂, h₃⟩ := readMoreOperands_reads succs vs _ rest
      (by simpa using h) hs
    rw [readMoreOperands.eq_1]
    simp only [h₁, ok_bind]
    simp only [Prod.mk.injEq] at h₂
    exact ⟨_, _, rfl, by simp [eraseAt, h₂.1, h₂.2], h₃⟩

/-- `readOperands` reads an op's operands, then its successors, as they are
written: separated by commas. -/
theorem readOperands_reads (operands : List Name) (succs : List Succ) :
    Reads readOperands (fun r => (r.1.map eraseAt, r.2)) (operands.map (·, TextPos.zero), succs)
      ([Tok.comma].intercalate (operands.map ([.value ·]) ++ succs.map Succ.tokens)) EndsUses := by
  intro ts rest h hs
  cases operands with
  | cons v vs =>
    rw [List.map_cons, List.cons_append, intercalate_cons, List.flatMap_append,
      flatMap_comma_map, flatMap_comma_map] at h
    simp only [List.cons_append, List.nil_append, List.append_assoc] at h
    take_tok h
    obtain ⟨⟨vs', ss⟩, ⟨r, hr⟩, h₁, h₂, h₃⟩ := readMoreOperands_reads succs vs _ rest
      (by simpa using h) hs
    rw [readOperands.eq_1]
    simp only [h₁, ok_bind]
    simp only [Prod.mk.injEq] at h₂
    exact ⟨_, _, rfl, by simp [eraseAt, h₂.1, h₂.2], h₃⟩
  | nil =>
    cases succs with
    | nil =>
      simp only [List.map_nil, List.append_nil, List.intercalate_nil, List.nil_append] at h
      rw [readOperands.eq_3 _
        (fun v p rest' he => by subst he; simpa [EndsUses] using hs (.value v) (by rw [← h]; rfl))
        (fun l p rest' he => by subst he; simpa [EndsUses] using hs (.label l) (by rw [← h]; rfl))]
      exact ⟨_, _, rfl, rfl, h⟩
    | cons s ss =>
      rw [List.map_nil, List.nil_append, List.map_cons, intercalate_cons, flatMap_comma_map,
        List.append_assoc] at h
      have h' : ts.map (·.tok) = .label s.label :: ((s.tokens.drop 1) ++
          (ss.flatMap (.comma :: Succ.tokens ·) ++ rest)) := by
        rw [h, Succ.tokens, List.cons_append, List.drop_one, List.tail_cons]
      obtain ⟨p, ts', rfl, -⟩ := map_tok_cons h'
      obtain ⟨s', ⟨r, hr⟩, h₁, h₂, h₃⟩ := Succ.reads s _ (ss.flatMap (.comma :: Succ.tokens ·) ++ rest)
        h (head?_append _ (by cases ss <;> simp) fun t ht => (hs t ht).ne.2)
      obtain ⟨ss', ⟨r', hr'⟩, h₄, h₅, h₆⟩ := readMore_succs ss r rest h₃ hs
      rw [readOperands.eq_2]
      simp only [h₁, ok_bind, h₄]
      exact ⟨_, _, rfl, by simp_all, h₆⟩

/-- `readOpLoc` reads an op's location reference. -/
theorem readOpLoc_reads (loc : LocRef) : Reads readOpLoc id loc [.locRef loc] (fun _ => True) := by
  intro ts rest h _
  simp only [List.cons_append, List.nil_append] at h
  take_tok h
  rw [readOpLoc.eq_1]
  exact ⟨_, _, rfl, rfl, h⟩

end Fir.Text
