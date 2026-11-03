import Fir.Text.Tree
import Fir.Text.LexWellFormed

/-!
# Reading printed tokens

The grammar step of the proof reads a module's tokens, `Module.tokens`, at
any positions, with the readers of the grammar sections. Most readers read
as long as a token follows that continues what they read: `readAttrs` while
an attribute follows, `readMore` while a comma follows, `readOps` while a
value or a word follows, and so on. A word followed by `(` is an applied
attribute or type. So whether a reader reads a construct's tokens as the
construct depends on the token after them, as maximal munch does for the
lexer, and each lemma says which tokens may follow. The printer puts one
there that stops the reader: a comma, a parenthesis, a brace, `=`, a label,
a location reference or the word `locs`.

`Reads read f x toks stop` says that on any tokens that hold `toks`, then
tokens whose first, if any, satisfies `stop`, `read` gives a result that `f`
maps to `x`, and leaves exactly the tokens after `toks`. The positions of
the tokens are any: `f` erases the ones the result holds.

The grammar step needs nothing of a module's names, words or numbers but
two things. Each type it writes is written as a word or an applied word
(`Attr.IsType`), since `readType` reads only those; and each line and
column of its location table is below `2^32`, since `readNat` reads only
those. A name that is not a word, a label that is not a name or a location
reference of `2^32` reads back as itself: the lexer, not the grammar,
rejects those.
-/

namespace Fir.Text

/-- `read` reads the tokens `toks`, at any positions, as what `f` maps to
`x`, before tokens whose first one satisfies `stop`. -/
def Reads {α β : Type} (read : (ts : List Token) → Read α ts) (f : α → β) (x : β)
    (toks : List Tok) (stop : Tok → Prop) : Prop :=
  ∀ ts rest, ts.map (·.tok) = toks ++ rest → (∀ t ∈ rest.head?, stop t) →
    ∃ a r, read ts = .ok (a, r) ∧ f a = x ∧ r.1.map (·.tok) = rest

/-- Tokens that hold `t` first start with `t`, at some position. -/
theorem map_tok_cons {ts : List Token} {t : Tok} {rest : List Tok}
    (h : ts.map (·.tok) = t :: rest) : ∃ p ts', ts = ⟨t, p⟩ :: ts' ∧ ts'.map (·.tok) = rest := by
  obtain ⟨⟨t', p⟩, ts', rfl, rfl, h'⟩ := List.map_eq_cons_iff.mp h
  exact ⟨p, ts', rfl, h'⟩

/-- Takes the first token off `h : ts.map (·.tok) = t :: rest`: `ts` becomes
`⟨t, p⟩ :: ts'`, and `h` says that `ts'.map (·.tok) = rest`. -/
local macro "take_tok " h:ident : tactic => `(tactic| (
  (try dsimp only at $h:ident)
  replace $h:ident := map_tok_cons $h
  obtain ⟨_, _, he, $h:ident⟩ := $h
  subst he))

/-- Tokens whose first is not `t` do not start with `t`. -/
theorem not_cons_of_head {ts : List Token} {rest : List Tok} {t : Tok}
    (h : ts.map (·.tok) = rest) (hs : ∀ u ∈ rest.head?, u ≠ t) :
    ∀ p ts', ts = ⟨t, p⟩ :: ts' → False := by
  intro p ts' he
  subst he
  exact hs t (by simp [← h]) rfl

/-- A list written with a separator: its first element, then each other one
after the separator. -/
theorem intercalate_cons {α : Type} (sep : α) (l : List α) (ls : List (List α)) :
    [sep].intercalate (l :: ls) = l ++ ls.flatMap (sep :: ·) := by
  induction ls generalizing l with
  | nil => simp
  | cons l' ls ih => rw [List.intercalate_cons_cons, ih]; simp

/-- What a list of tokens starts with, when it starts with a list. -/
theorem head?_append {ts rest : List Tok} (P : Tok → Prop) (h₁ : ∀ t ∈ ts.head?, P t)
    (h₂ : ∀ t ∈ rest.head?, P t) : ∀ t ∈ (ts ++ rest).head?, P t := by
  cases ts with
  | nil => simpa using h₂
  | cons t ts => simpa using h₁

/-- Reading the token that `expect` expects. -/
theorem expect_cons (tok : Tok) (e : String) (p : TextPos) (ts : List Token) :
    expect tok e (⟨tok, p⟩ :: ts) = .ok ((), ⟨ts, Nat.le_succ _⟩) := by
  simp [expect]

/-- `readMore item` reads `, x` for each `x` of a list, when `item` reads
each `x` before a comma and before what follows the list. -/
theorem Reads.more {α β γ : Type} {item : (ts : List Token) → Read α ts} {f : α → β}
    {g : γ → β} {toks : γ → List Tok} {stop stop' : Tok → Prop} (hc : stop .comma)
    (hs : ∀ t, stop' t → stop t ∧ t ≠ .comma) :
    ∀ {xs : List γ}, (∀ x ∈ xs, Reads item f (g x) (toks x) stop) →
      Reads (readMore item) (List.map f) (xs.map g) (xs.flatMap (.comma :: toks ·)) stop'
  | [], _, ts, rest, h, hst => by
    simp only [List.flatMap_nil, List.nil_append] at h
    rw [readMore.eq_2 _ _ (not_cons_of_head h fun u hu => (hs u (hst u hu)).2)]
    exact ⟨[], _, rfl, rfl, h⟩
  | x :: xs, hx, ts, rest, h, hst => by
    simp only [List.flatMap_cons, List.cons_append, List.append_assoc] at h
    take_tok h
    obtain ⟨a, ⟨r, hr⟩, h₁, h₂, h₃⟩ := hx x (.head _) _ (xs.flatMap (.comma :: toks ·) ++ rest) h
      (head?_append _ (by cases xs <;> simp [hc]) fun t ht => (hs t (hst t ht)).1)
    obtain ⟨as, ⟨r', hr'⟩, h₄, h₅, h₆⟩ :=
      Reads.more hc hs (fun y hy => hx y (.tail _ hy)) r rest h₃ hst
    rw [readMore.eq_1]
    simp only [h₁, ok_bind, h₄]
    exact ⟨_, _, rfl, by simp [h₂, ← h₅], h₆⟩

/-! # Attributes and types -/

/-- An attribute's tokens start with a token that starts an attribute. -/
theorem Attr.tokens_cons (a : Attr) : ∃ t ts, a.tokens = t :: ts ∧ t.startsAttr = true := by
  cases a <;> exact ⟨_, _, rfl, rfl⟩

/-- The tokens of attributes, each after a comma. -/
abbrev commaAttrs (as : List Attr) : List Tok := (Attr.tokens.tokensList as).flatMap (.comma :: ·)

mutual
/-- `readAttr` reads an attribute's tokens as the attribute, before any
token but `(`. -/
theorem Attr.reads : ∀ (a : Attr) (ts : List Token) (rest : List Tok),
    ts.map (·.tok) = a.tokens ++ rest → (∀ t ∈ rest.head?, t ≠ .lparen) →
    ∃ r, readAttr ts = .ok (a, r) ∧ r.1.map (·.tok) = rest
  | .word w, ts, rest, h, hs => by
    simp only [Attr.tokens, List.singleton_append] at h
    take_tok h
    rw [readAttr.eq_2 _ _ _ (not_cons_of_head h hs)]
    exact ⟨_, rfl, h⟩
  | .int i, ts, rest, h, _ => by
    simp only [Attr.tokens, List.singleton_append] at h
    take_tok h
    rw [readAttr.eq_3]
    exact ⟨_, rfl, h⟩
  | .str s, ts, rest, h, _ => by
    simp only [Attr.tokens, List.singleton_append] at h
    take_tok h
    rw [readAttr.eq_4]
    exact ⟨_, rfl, h⟩
  | .sym s, ts, rest, h, _ => by
    simp only [Attr.tokens, List.singleton_append] at h
    take_tok h
    rw [readAttr.eq_5]
    exact ⟨_, rfl, h⟩
  | .app w args, ts, rest, h, _ => by
    simp only [Attr.tokens, List.cons_append, List.append_assoc] at h
    take_tok h
    take_tok h
    obtain ⟨⟨r, hr⟩, h₁, h₂⟩ := Attr.readsArgs args _ rest h
    rw [readAttr.eq_1]
    simp only [h₁, ok_bind]
    exact ⟨_, rfl, h₂⟩

/-- `readAttrArgs` reads the tokens of an applied attribute's arguments,
then `)`, as the arguments. -/
theorem Attr.readsArgs : ∀ (as : List Attr) (ts : List Token) (rest : List Tok),
    ts.map (·.tok) = [Tok.comma].intercalate (Attr.tokens.tokensList as) ++ .rparen :: rest →
    ∃ r, readAttrArgs ts = .ok (as, r) ∧ r.1.map (·.tok) = rest
  | [], ts, rest, h => by
    simp only [Attr.tokens.tokensList, List.intercalate_nil, List.nil_append] at h
    take_tok h
    rw [readAttrArgs.eq_1]
    exact ⟨_, rfl, h⟩
  | a :: as, ts, rest, h => by
    rw [Attr.tokens.tokensList, intercalate_cons, List.append_assoc] at h
    obtain ⟨t, us, he, hst⟩ := Attr.tokens_cons a
    have hne : ∀ p ts', ts = ⟨.rparen, p⟩ :: ts' → False := fun p ts' he' => by
      subst he'
      rw [he] at h
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
      rw [← h.1] at hst
      exact Bool.false_ne_true hst
    obtain ⟨⟨r, hr⟩, h₁, h₂⟩ := Attr.reads a ts (commaAttrs as ++ .rparen :: rest) h
      (head?_append _ (by cases as <;> simp [commaAttrs, Attr.tokens.tokensList]) (by simp))
    obtain ⟨⟨r', hr'⟩, h₃, h₄⟩ := Attr.readsMoreArgs as r rest h₂
    rw [readAttrArgs.eq_2 _ hne]
    simp only [h₁, ok_bind, h₃]
    exact ⟨_, rfl, h₄⟩

/-- `readMoreAttrArgs` reads `, a` for each argument `a`, then `)`, as the
arguments. -/
theorem Attr.readsMoreArgs : ∀ (as : List Attr) (ts : List Token) (rest : List Tok),
    ts.map (·.tok) = commaAttrs as ++ .rparen :: rest →
    ∃ r, readMoreAttrArgs ts = .ok (as, r) ∧ r.1.map (·.tok) = rest
  | [], ts, rest, h => by
    simp only [commaAttrs, Attr.tokens.tokensList, List.flatMap_nil, List.nil_append] at h
    take_tok h
    rw [readMoreAttrArgs.eq_2]
    exact ⟨_, rfl, h⟩
  | a :: as, ts, rest, h => by
    simp only [commaAttrs, Attr.tokens.tokensList, List.flatMap_cons, List.cons_append,
      List.append_assoc] at h
    take_tok h
    obtain ⟨⟨r, hr⟩, h₁, h₂⟩ := Attr.reads a _ (commaAttrs as ++ .rparen :: rest) h
      (head?_append _ (by cases as <;> simp [commaAttrs, Attr.tokens.tokensList]) (by simp))
    obtain ⟨⟨r', hr'⟩, h₃, h₄⟩ := Attr.readsMoreArgs as r rest h₂
    rw [readMoreAttrArgs.eq_1]
    simp only [h₁, ok_bind, h₃]
    exact ⟨_, rfl, h₄⟩
end

/-- `readType` reads a type's tokens as the type, before any token but
`(`. -/
theorem readType_reads {a : Attr} (ha : a.IsType) :
    Reads readType eraseAt (a, .zero) a.tokens (· ≠ .lparen) := by
  intro ts rest h hs
  cases a with
  | word w =>
    simp only [Attr.tokens, List.singleton_append] at h
    take_tok h
    rw [readType.eq_2 _ _ _ (not_cons_of_head h hs)]
    exact ⟨_, _, rfl, rfl, h⟩
  | app w args =>
    simp only [Attr.tokens, List.cons_append, List.append_assoc] at h
    take_tok h
    take_tok h
    obtain ⟨⟨r, hr⟩, h₁, h₂⟩ := Attr.readsArgs args _ rest h
    rw [readType.eq_1]
    simp only [h₁, ok_bind]
    exact ⟨_, _, rfl, rfl, h₂⟩
  | _ => exact absurd ha id

/-- `readAttrs` reads the tokens of attributes as the attributes, before a
token that starts no attribute and is not `(`. -/
theorem readAttrs_reads :
    ∀ as : List Attr, Reads readAttrs (List.map (·.1)) as (as.flatMap Attr.tokens)
      (fun t => t.startsAttr = false ∧ t ≠ .lparen)
  | [], ts, rest, h, hs => by
    simp only [List.flatMap_nil, List.nil_append] at h
    match ts, h with
    | [], h =>
      rw [readAttrs.eq_2]
      exact ⟨[], _, rfl, rfl, h⟩
    | t :: ts', h =>
      have ht : t.tok.startsAttr = false := (hs t.tok (by simp [← h])).1
      rw [readAttrs.eq_1]
      simp only [ht, Bool.false_eq_true, ite_false]
      exact ⟨[], _, rfl, rfl, h⟩
  | a :: as, ts, rest, h, hs => by
    simp only [List.flatMap_cons, List.append_assoc] at h
    obtain ⟨t, us, he, hst⟩ := Attr.tokens_cons a
    have h' : ts.map (·.tok) = t :: (us ++ (as.flatMap Attr.tokens ++ rest)) := by
      rw [h, he, List.cons_append]
    obtain ⟨p, ts', rfl, -⟩ := map_tok_cons h'
    obtain ⟨⟨r, hr⟩, h₁, h₂⟩ := Attr.reads a _ _ h fun u hu => by
      cases as with
      | nil => exact (hs u (by simpa using hu)).2
      | cons a' as' =>
        obtain ⟨t', us', he', hst'⟩ := Attr.tokens_cons a'
        simp only [List.flatMap_cons, he', List.cons_append, List.head?_cons,
          Option.mem_def, Option.some.injEq] at hu
        subst hu
        intro hl
        rw [hl] at hst'
        exact Bool.false_ne_true hst'
    obtain ⟨as', ⟨r', hr'⟩, h₃, h₄, h₅⟩ := readAttrs_reads as r rest h₂ hs
    rw [readAttrs.eq_1]
    simp only [hst, ite_true, h₁, ok_bind, h₃]
    exact ⟨_, _, rfl, by simp [h₄], h₅⟩

end Fir.Text
