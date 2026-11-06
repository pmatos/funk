import Fir.Text.LexTokens

/-!
# Why every parsed module is well formed

The round trip shows that parsing the printed form of a well-formed module
gives the module back. These nine sections, from this one to the one on
parsed modules, prove a converse: every module that the parser gives is
well formed, whatever text it read, whoever wrote it, with comments, with
any spacing, or without its final line feed.

It matters because a well-formed module is exactly one whose printed form
says everything it holds. Without this result, the parser could accept a
text and give a module that the printer cannot write faithfully: one that
defines a value twice, that names a value with something other than a
name, or that holds a location number that does not fit in 32 bits.
Printing such a module would give a text that reads back as another module,
or not at all. With this result and the round trip, printing what the
parser reads is idempotent on every text that it accepts: formatting a
text twice gives what formatting it once gives, and every tool that reads
fir text gets a module that it can write back as it is.

The proof follows the parser's three steps, as the round trip's does
(ADR-2026-11-03-0028), and each step gives what the next one needs:

1. the lexer reads only tokens that can be written: value names and labels
   made of one or more name characters, words that start with a letter or
   `_`, and location references below 2³². This section proves it;
2. on tokens that can be written, the grammar reads a tree that can be
   written: the sections on what the grammar accepts, on accepted ops,
   blocks and regions, on accepted items, and on an accepted location
   table;
3. a tree that can be written decodes to a well-formed module: the
   sections on what the first pass accepts, on what the second pass
   accepts, and on what decoding accepts.

The section on parsed modules joins the three steps.

# Every token read can be written

The lexer reads no token that cannot be written. A value or a label is `%`
or `^` and the name characters after it, and the lexer rejects it when
there are none. A word starts with a letter or `_` and takes in every name
character after it. A location reference of 2³² or more is an error at
the number. Symbols, integers, strings and punctuation can all be written,
and whitespace and comments give no token at all.
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
