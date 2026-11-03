import Fir.Text.LexTokens

/-!
# Every token read can be written

The round trip, `printThenParse`, reads back what the printer writes. This
section and the ones after it prove a converse for every text that the
parser accepts, whoever wrote it, with comments and any spacing: if
`Fir.parse t = .ok m`, then `m` is well formed (`parse_wellFormed`, in the
section "Parsed modules are well formed"). With the round trip, printing
what the parser reads is then idempotent on every text that it accepts.

The proof follows the parser's three steps, as the round trip's does
(ADR-2026-11-03-0028). Each step gives what the next one needs:

1. every token that the lexer reads, but `eof`, can be written
   (`lex_writable`, below);
2. on tokens that can be written, `readModule` gives a tree that can be
   written (`readModule_writable`);
3. a tree that can be written decodes to a well-formed module
   (`decodeModule_wellFormed`).

A token can be written when `Tok.Writable` holds of it: a value name or a
label is a name, a word is a word, and a location reference is below
`2^32`. The lexer reads no other token. A value or a label is `%` or `^`
and the name characters after it, and `lexToken` rejects it when there are
none. A word starts with a letter or `_` and takes in every name character
after it. A location reference of `2^32` or more is an error at the number
(`lexAt`). Symbols, integers, strings and punctuation can all be written.
Whitespace and comments give no token at all.

Each lemma is about one function of the lexer, and says that a token it
reads can be written. `bind_eq_ok` takes a step of a reader apart: when a
step and what follows it succeed, the step succeeded. The proofs of all
three steps use it, through the tactic `bind_step`.
-/

namespace Fir.Text

/-- When a step and what follows it succeed, the step succeeded, and what
follows succeeded on its result. -/
theorem bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- Takes the first step of `h : (x >>= f) = .ok b` apart with `bind_eq_ok`:
`pat` matches the result `a` of `x`, the equation `x = .ok a`, and the
equation `f a = .ok b`. `h` itself is dropped, so that the goals of the
proofs that use it do not hold each step's program twice. -/
scoped macro "bind_step " h:ident " with " pat:Lean.Parser.Tactic.rcasesPatMed : tactic =>
  `(tactic| (
    replace $h:ident := Fir.Text.bind_eq_ok $h:ident
    obtain $pat := $h:ident))

/-- The characters that `takeWhile` takes satisfy its test. -/
theorem mem_takeWhile {p : Char → Bool} :
    ∀ {cs : List Char} {c : Char}, c ∈ cs.takeWhile p → p c = true
  | [], _, h => by simp at h
  | x :: xs, c, h => by
    rw [List.takeWhile_cons] at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · assumption
      · exact mem_takeWhile h
    · simp at h

/-- The name characters at the start of some characters are a name, when
there is one. -/
theorem isName_takeWhile {cs : List Char} (h : ¬(cs.takeWhile isNameChar).isEmpty = true) :
    isName (String.ofList (cs.takeWhile isNameChar)) = true :=
  isName_iff.mpr ⟨by simpa using h, fun _ hc => mem_takeWhile (by simpa using hc)⟩

/-- A character that starts a word, then the name characters after it, is a
word. -/
theorem isWord_takeWhile {c : Char} {cs : List Char} (h : isWordStart c = true) :
    isWord (String.ofList (c :: cs.takeWhile isNameChar)) = true := by
  simp only [isWord, String.toList_ofList, h, Bool.true_and, List.all_eq_true]
  exact fun _ hc => mem_takeWhile hc

/-- `lexInt` reads an integer, which can be written. -/
theorem lexInt_writable {neg : Bool} {d : Char} {cs : List Char} {p : TextPos} {t : Tok}
    {r : Left cs} {q : TextPos} (h : lexInt neg d cs p = .ok (t, r, q)) : t.Writable := by
  unfold lexInt at h
  bind_step h with ⟨_, -, h⟩
  cases h
  exact True.intro

/-- What follows `@` is a location reference below `2^32`, or a symbol. -/
theorem lexAt_writable {cs : List Char} {p : TextPos} {t : Tok} {r : Left cs} {q : TextPos}
    (h : lexAt cs p = .ok (t, r, q)) : t.Writable := by
  unfold lexAt at h
  rcases cs with _ | ⟨c, rest⟩
  · cases h
  dsimp only at h
  split at h
  · bind_step h with ⟨⟨_, _⟩, -, h⟩
    dsimp only at h
    split at h
    · cases h; assumption
    · cases h
  split at h
  · cases h; exact True.intro
  split at h
  · bind_step h with ⟨⟨_, _⟩, -, h⟩
    dsimp only at h
    split at h
    · cases h
    · cases h; exact True.intro
  · cases h

/-- Every token that `lexToken` reads can be written. -/
theorem lexToken_writable {c : Char} {cs : List Char} {p : TextPos} {t : Tok} {r : Left cs}
    {q : TextPos} (h : lexToken c cs p = .ok (t, r, q)) : t.Writable := by
  unfold lexToken at h
  -- Punctuation, then a character that is not allowed outside strings.
  split at h
  all_goals dsimp only at h
  all_goals split at h
  all_goals try (cases h; done)
  any_goals (cases h; exact True.intro)
  -- A value or a label.
  split at h
  · split at h
    · cases h
    · split at h <;> cases h <;> exact isName_takeWhile ‹_›
  -- `@`, a string, `-`, a digit and a word.
  split at h
  · exact lexAt_writable h
  split at h
  · bind_step h with ⟨_, -, h⟩
    cases h; exact True.intro
  split at h
  · split at h
    · cases h; exact True.intro
    · cases h
    · split at h
      · bind_step h with ⟨⟨_, _, _⟩, h₁, h⟩
        cases h
        exact lexInt_writable h₁
      · cases h
    · cases h
  split at h
  · exact lexInt_writable h
  split at h
  · cases h; exact isWord_takeWhile ‹_›
  · cases h

/-- Every token of `ts` but `eof` can be written. The lexer ends every list
it gives with `eof`, and the readers read it only to check that the text
has ended. -/
def TokensWritable (ts : List Token) : Prop := ∀ t ∈ ts, t.tok = .eof ∨ t.tok.Writable

/-- `lexFrom` reads only tokens that can be written, then `eof`, after
tokens that can be written. -/
theorem lexFrom_writable : ∀ (cs : List Char) (p : TextPos) (acc : List Token),
    (∀ t ∈ acc, t.tok.Writable) → ∀ ts, lexFrom cs p acc = .ok ts → TokensWritable ts := by
  intro cs p acc
  induction cs, p, acc using lexFrom.induct with
  | case1 p acc =>
    intro ha ts h
    rw [lexFrom] at h
    cases h
    intro t ht
    simp only [List.reverse_cons, List.mem_append, List.mem_reverse, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact .inr (ha t ht)
    · exact .inl rfl
  | case2 p acc rest ih | case3 p acc rest ih | case4 p acc rest ih =>
    intro ha ts h
    rw [lexFrom] at h
    exact ih ha ts h
  | case5 p acc rest body c n hc =>
    intro ha ts h
    rw [lexFrom] at h
    split at h
    · cases h
    · exact absurd hc (by simp_all [body])
  | case6 p acc rest body hn _ ih =>
    intro ha ts h
    rw [lexFrom] at h
    split at h
    · exact absurd hn (by simp_all [body])
    · exact ih ha ts h
  | case7 p acc c rest h1 h2 h3 h4 ih =>
    intro ha ts h
    rw [lexFrom.eq_6 _ _ _ _ h1 h2 h3 h4] at h
    bind_step h with ⟨⟨t, ⟨r, hr⟩, q⟩, h₁, h⟩
    refine ih t r hr q ?_ ts h
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact lexToken_writable h₁
    · exact ha u hu

/-- The lexer's step: every token that the lexer reads from a text, but
`eof`, can be written. -/
theorem lex_writable {text : String} {ts : List Token} (h : lex text = .ok ts) :
    TokensWritable ts :=
  lexFrom_writable _ _ _ (by simp) ts h

end Fir.Text
