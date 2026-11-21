import Fir.Text.ReadDefs

/-!
# Reading a signature's parameters and results

A parameter's tokens, its definition and then its attributes, read back as
its tree and its attributes, before any token that starts no attribute and
is not `(`; so do a result's, its type and then its attributes. The
parameters of an item, separated by commas and ending in `, ...` or `...`
when the item is variadic, read back before its `)`.

The grammar reads the attributes after an item's last result as the item's
attributes. An item of a dialect's kind writes its attributes there, so it
reads back as if its last result carried them and every other result none
(`lastAttrs`).
-/

namespace Fir.Text

variable {d : Dialect} [DialectText d]

/-- A parameter as read, without positions: its definition and its
attributes. -/
def eraseParam (p : SDef × List (Attr × TextPos)) : SDef × List Attr :=
  (p.1.erase, p.2.map (·.1))

/-- A parameter's tree and its attributes. -/
def paramTree (p : (Name × d.Ty) × List Attr) : SDef × List Attr := (defTree p.1, p.2)

/-- The tokens of a parameter: its definition, then its attributes. -/
def paramToks (p : (Name × d.Ty) × List Attr) : List Tok := defTokens p.1 ++ p.2.flatMap Attr.tokens

/-- The tokens of attributes start with a token that starts an attribute. -/
theorem attrs_head (as : List Attr) : ∀ t ∈ (as.flatMap Attr.tokens).head?, t.startsAttr = true := by
  intro t ht
  rcases as with _ | ⟨a, as⟩
  · simp at ht
  · obtain ⟨u, us, he, hu⟩ := Attr.tokens_cons a
    simp only [List.flatMap_cons, he, List.cons_append, List.head?_cons, Option.mem_def,
      Option.some.injEq] at ht
    exact ht ▸ hu

/-- The tokens of attributes do not start with `(`. -/
theorem attrs_head_ne (as : List Attr) : ∀ t ∈ (as.flatMap Attr.tokens).head?, t ≠ .lparen :=
  fun t ht hl => by have := attrs_head as t ht; rw [hl] at this; exact Bool.false_ne_true this

/-- `readParam` reads a parameter's tokens as its tree and attributes. -/
theorem readParam_reads {p : (Name × d.Ty) × List Attr} (hx : (tyAttr p.1.2).IsType) :
    Reads readParam eraseParam (paramTree p) (paramToks p)
      (fun t => t.startsAttr = false ∧ t ≠ .lparen) := by
  intro ts rest h hs
  simp only [paramToks, List.append_assoc] at h
  obtain ⟨sd, ⟨r, hr⟩, h₁, h₂, h₃⟩ := readDef_reads hx ts (p.2.flatMap Attr.tokens ++ rest) h
    (head?_append _ (attrs_head_ne p.2) fun t ht => (hs t ht).2)
  obtain ⟨as, ⟨r', hr'⟩, h₄, h₅, h₆⟩ := readAttrs_reads p.2 r rest h₃ hs
  simp only [readParam, h₁, ok_bind, h₄]
  exact ⟨_, _, rfl, by simp [eraseParam, paramTree, h₂, h₅], h₆⟩

/-- The tokens of `...` at the end of parameters: none when they do not end
in it, and a comma before it when a parameter comes first. -/
def ellipsisToks (first variadic : Bool) : List Tok :=
  if variadic then (if first then [.ellipsis] else [.comma, .ellipsis]) else []

/-- `readMoreParams` reads `, p` for each parameter `p` and `, ...` when the
parameters end in it, before `)`. -/
theorem readMoreParams_reads (v : Bool) : ∀ {ps : List ((Name × d.Ty) × List Attr)},
    (∀ p ∈ ps, (tyAttr p.1.2).IsType) →
    Reads readMoreParams (fun r => (r.1.map eraseParam, r.2.isSome)) (ps.map paramTree, v)
      (ps.flatMap (.comma :: paramToks ·) ++ ellipsisToks false v) (· = .rparen)
  | [], _, ts, rest, h, hs => by
    cases v
    · simp only [List.flatMap_nil, ellipsisToks, Bool.false_eq_true, ite_false,
        List.append_nil, List.nil_append] at h
      match ts, h with
      | [], h =>
        rw [readMoreParams.eq_3 _ (by intro _ _ _ he; cases he) (by intro _ _ he; cases he)]
        exact ⟨_, _, rfl, rfl, h⟩
      | t :: ts', h =>
        have ht : t.tok = .rparen := hs t.tok (by simp [← h])
        obtain ⟨tok, q⟩ := t
        simp only at ht
        subst ht
        rw [readMoreParams.eq_3 _ (by intro _ _ _ he; cases he) (by intro _ _ he; cases he)]
        exact ⟨_, _, rfl, rfl, h⟩
    · simp only [List.flatMap_nil, ellipsisToks, ite_true, Bool.false_eq_true, ite_false,
        List.nil_append, List.cons_append] at h
      take_tok h
      take_tok h
      rw [readMoreParams.eq_1]
      exact ⟨_, _, rfl, rfl, h⟩
  | p :: ps, hx, ts, rest, h, hs => by
    simp only [List.flatMap_cons, List.cons_append, List.append_assoc] at h
    take_tok h
    obtain ⟨sp, ⟨r, hr⟩, h₁, h₂, h₃⟩ := readParam_reads (hx p (.head _)) _
      (ps.flatMap (.comma :: paramToks ·) ++ (ellipsisToks false v ++ rest)) h
      (head?_append _ (by cases ps <;> simp [Tok.startsAttr]) (head?_append _
        (by cases v <;> simp [ellipsisToks, Tok.startsAttr]) fun t ht => by
          rw [hs t ht]; simp [Tok.startsAttr]))
    obtain ⟨⟨sps, v'⟩, ⟨r', hr'⟩, h₄, h₅, h₆⟩ :=
      readMoreParams_reads v (fun q hq => hx q (.tail _ hq)) r rest (by simpa using h₃) hs
    rw [readMoreParams.eq_2 _ _ (by
      intro q' rest' he
      subst he
      simp [paramToks, defTokens] at h)]
    simp only [h₁, ok_bind, h₄]
    simp only [Prod.mk.injEq] at h₅
    exact ⟨_, _, rfl, by simp [h₂, h₅.1, h₅.2], h₆⟩

/-- The tokens of an item's parameters, before its `)`: each parameter,
separated by commas, then `...` when they end in it. -/
def paramsToks (ps : List ((Name × d.Ty) × List Attr)) (v : Bool) : List Tok :=
  [Tok.comma].intercalate (ps.map paramToks) ++ ellipsisToks ps.isEmpty v

/-- `readParams` reads an item's parameters, before its `)`, when there is
one or they end in `...`. -/
theorem readParams_reads {ps : List ((Name × d.Ty) × List Attr)} {v : Bool}
    (hne : ps ≠ [] ∨ v = true) (hx : ∀ p ∈ ps, (tyAttr p.1.2).IsType) :
    Reads readParams (fun r => (r.1.map eraseParam, r.2.isSome)) (ps.map paramTree, v)
      (paramsToks ps v) (· = .rparen) := by
  intro ts rest h hs
  rcases ps with _ | ⟨p, ps⟩
  · obtain rfl : v = true := hne.resolve_left (by simp)
    simp only [paramsToks, List.map_nil, List.intercalate_nil, List.isEmpty_nil, ellipsisToks,
      ite_true, List.nil_append, List.cons_append] at h
    take_tok h
    rw [readParams.eq_1]
    exact ⟨_, _, rfl, rfl, h⟩
  · simp only [paramsToks, List.map_cons, intercalate_cons, List.isEmpty_cons, List.append_assoc,
      flatMap_comma_map] at h
    obtain ⟨sp, ⟨r, hr⟩, h₁, h₂, h₃⟩ := readParam_reads (hx p (.head _)) _
      (ps.flatMap (.comma :: paramToks ·) ++ (ellipsisToks false v ++ rest)) h
      (head?_append _ (by cases ps <;> simp [Tok.startsAttr]) (head?_append _
        (by cases v <;> simp [ellipsisToks, Tok.startsAttr]) fun t ht => by
          rw [hs t ht]; simp [Tok.startsAttr]))
    obtain ⟨⟨sps, v'⟩, ⟨r', hr'⟩, h₄, h₅, h₆⟩ :=
      readMoreParams_reads v (fun q hq => hx q (.tail _ hq)) r rest (by simpa using h₃) hs
    rw [readParams.eq_2 _ (by
      intro q' rest' he
      subst he
      simp [paramToks, defTokens] at h)]
    simp only [h₁, ok_bind, h₄]
    simp only [Prod.mk.injEq] at h₅
    exact ⟨_, _, rfl, by simp [h₂, h₅.1, h₅.2], h₆⟩

/-- A result as read, without positions: its type and its attributes. -/
def eraseResult (r : (Attr × TextPos) × List (Attr × TextPos)) : (Attr × TextPos) × List Attr :=
  (eraseAt r.1, r.2.map (·.1))

/-- The tokens of a result: its type, then its attributes. -/
def resultToks (r : Attr × List Attr) : List Tok := r.1.tokens ++ r.2.flatMap Attr.tokens

/-- `readResult` reads a result's tokens as its type and attributes. -/
theorem readResult_reads {r : Attr × List Attr} (ha : r.1.IsType) :
    Reads readResult eraseResult ((r.1, .zero), r.2) (resultToks r)
      (fun t => t.startsAttr = false ∧ t ≠ .lparen) := by
  intro ts rest h hs
  simp only [resultToks, List.append_assoc] at h
  obtain ⟨t, ⟨q, hq⟩, h₁, h₂, h₃⟩ := readType_reads ha ts (r.2.flatMap Attr.tokens ++ rest) h
    (head?_append _ (attrs_head_ne r.2) fun t ht => (hs t ht).2)
  obtain ⟨as, ⟨r', hr'⟩, h₄, h₅, h₆⟩ := readAttrs_reads r.2 q rest h₃ hs
  simp only [readResult, h₁, ok_bind, h₄]
  exact ⟨_, _, rfl, by simp [eraseResult, h₂, h₅], h₆⟩

/-- Places, each with no attributes but the last, which has `as`. -/
def lastAttrs {α : Type} : List α → List Attr → List (α × List Attr)
  | [], _ => []
  | [x], as => [(x, as)]
  | x :: y :: xs, as => (x, []) :: lastAttrs (y :: xs) as

theorem lastAttrs_fst {α : Type} : ∀ (xs : List α) (as : List Attr),
    (lastAttrs xs as).map (·.1) = xs
  | [], _ => rfl
  | [_], _ => rfl
  | x :: y :: xs, as => by simp [lastAttrs, lastAttrs_fst (y :: xs) as]

theorem lastAttrs_dropLast {α : Type} : ∀ (xs : List α) (as : List Attr),
    (lastAttrs xs as).dropLast.map (·.2) = xs.dropLast.map fun _ => []
  | [], _ => rfl
  | [_], _ => rfl
  | x :: y :: xs, as => by
    rw [lastAttrs, List.dropLast_cons_of_ne_nil (by cases xs <;> simp [lastAttrs]),
      List.dropLast_cons_of_ne_nil (by simp), List.map_cons, List.map_cons,
      lastAttrs_dropLast (y :: xs) as]

theorem lastAttrs_getLast {α : Type} : ∀ {xs : List α} (as : List Attr), xs ≠ [] →
    ((lastAttrs xs as).getLast?.map (·.2)).getD [] = as
  | [], _, h => absurd rfl h
  | [_], _, _ => rfl
  | x :: y :: xs, as, _ => by
    simp only [lastAttrs]
    rw [List.getLast?_cons_of_ne_nil (by cases xs <;> simp [lastAttrs])]
    exact lastAttrs_getLast as (by simp)

/-- The tokens of places written with a comma between each, then `as`: those
of each place with its attributes, the last carrying `as`. -/
theorem lastAttrs_tokens {α : Type} (g : α → List Tok) : ∀ {xs : List α} (as : List Attr),
    xs ≠ [] → [Tok.comma].intercalate (xs.map g) ++ as.flatMap Attr.tokens =
      [Tok.comma].intercalate ((lastAttrs xs as).map fun p => g p.1 ++ p.2.flatMap Attr.tokens)
  | [], _, h => absurd rfl h
  | [_], _, _ => by simp [lastAttrs]
  | x :: y :: xs, as, _ => by
    have ih := lastAttrs_tokens g as (xs := y :: xs) (by simp)
    obtain ⟨q, qs, hq⟩ : ∃ q qs, lastAttrs (y :: xs) as = q :: qs := by
      cases xs <;> simp [lastAttrs]
    have hl : lastAttrs (x :: y :: xs) as = (x, []) :: lastAttrs (y :: xs) as := rfl
    have e₁ : [Tok.comma].intercalate ((x :: y :: xs).map g) =
        g x ++ [Tok.comma] ++ [Tok.comma].intercalate ((y :: xs).map g) := by
      simp only [List.map_cons, List.intercalate_cons_cons]
    have e₂ : ∀ F : α × List Attr → List Tok,
        [Tok.comma].intercalate ((lastAttrs (x :: y :: xs) as).map F) =
          F (x, []) ++ [Tok.comma] ++ [Tok.comma].intercalate ((lastAttrs (y :: xs) as).map F) := by
      intro F
      rw [hl, hq]
      simp only [List.map_cons, List.intercalate_cons_cons]
    rw [e₁, e₂, ← ih]
    simp only [List.flatMap_nil, List.append_nil, List.append_assoc]

/-- Erasing the positions of attributes is writing their tree. -/
theorem map_eraseAt (l : List (Attr × TextPos)) : l.map eraseAt = attrsTree (l.map (·.1)) := by
  simp [attrsTree, eraseAt]

/-- What parameters as read hold, without positions: each definition and
its attributes. -/
theorem params_read {P : List (SDef × List (Attr × TextPos))}
    {PS : List ((Name × d.Ty) × List Attr)} (h : P.map eraseParam = PS.map paramTree) :
    (P.map (·.1)).map SDef.erase = (PS.map (·.1)).map defTree ∧
      (P.map (·.2)).map (·.map eraseAt) = (PS.map (·.2)).map attrsTree := by
  have h₁ := congrArg (List.map (·.1)) h
  have h₂ := congrArg (List.map (·.2)) h
  simp only [List.map_map, Function.comp_def, eraseParam, paramTree] at h₁ h₂
  refine ⟨by simpa [List.map_map, Function.comp_def] using h₁, ?_⟩
  have h₃ := congrArg (List.map attrsTree) h₂
  simpa [List.map_map, Function.comp_def, map_eraseAt] using h₃

/-- What results as read hold, without positions: each type and its
attributes, those of the last apart. -/
theorem results_read {R : List ((Attr × TextPos) × List (Attr × TextPos))}
    {RS : List (Attr × List Attr)} (h : R.map eraseResult = RS.map fun r => ((r.1, .zero), r.2)) :
    (R.map (·.1)).map eraseAt = RS.map (fun r => (r.1, .zero)) ∧
      (R.dropLast.map (·.2)).map (·.map eraseAt) = (RS.map (·.2)).dropLast.map attrsTree ∧
      ((R.getLast?.map (·.2)).getD []).map eraseAt =
        attrsTree (((RS.map (·.2)).getLast?).getD []) := by
  have h₁ := congrArg (List.map (·.1)) h
  have h₂ := congrArg (List.map (·.2)) h
  simp only [List.map_map, Function.comp_def, eraseResult] at h₁ h₂
  refine ⟨by simpa [List.map_map, Function.comp_def] using h₁, ?_, ?_⟩
  · have h₃ := congrArg (fun l => l.dropLast.map attrsTree) h₂
    simp only [← List.map_dropLast, List.map_map, Function.comp_def] at h₃
    simpa [List.map_map, Function.comp_def, map_eraseAt] using h₃
  · have h₃ := congrArg (fun l => attrsTree (l.getLast?.getD [])) h₂
    simp only [List.getLast?_map] at h₃
    rw [map_eraseAt, List.getLast?_map, ← h₃]
    rcases R.getLast? with _ | r <;> rfl

end Fir.Text
