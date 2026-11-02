import Fir.Text.ReadFunc
import Fir.Text.ReadTable

/-!
# Reading a printed module

A module's items read back before the word `locs`, which starts its
location table, and the table before `eof`. Each item of M0 is a function,
which the previous section reads.

The result is `readModule_tokens`: on any tokens with the module's
`Module.tokens`, then `eof`, at any positions, `readModule` gives a tree
that is the module's tree once its positions are erased. It needs only that
each type the module writes is written as a type, and that its location
table is within the limits. A well-formed module has both
(`Module.WellFormed.readModule_tokens`), so with `lex_print` the first two
steps of the parser read its printed text as its tree
(`Module.WellFormed.read_print`). The last step decodes that tree; that it
gives the module back is the next step of #11.
-/

namespace Fir

open Text

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

/-- `readItems` reads the tokens of a module's items as their trees, before
the word `locs`. -/
theorem readItems_reads : ∀ items : List (Item d),
    (∀ f, Item.func f ∈ items → ∀ t ∈ f.types, (tyAttr t).IsType) →
    Reads (readItems true) SItem.eraseList (items.map Item.tree) (items.flatMap Item.tokens)
      (· = .word "locs")
  | [], _, ts, rest, h, hs => by
    simp only [List.flatMap_nil, List.nil_append] at h
    match ts, h with
    | [], h =>
      rw [readItems.eq_2 _ _ fun _ _ _ he => by simp at he]
      exact ⟨[], _, rfl, rfl, h⟩
    | ⟨t, p⟩ :: ts', h =>
      have ht : t = .word "locs" := hs t (by simp [← h])
      subst ht
      rw [readItems.eq_1]
      exact ⟨[], _, rfl, rfl, h⟩
  | .func f :: items, ht, ts, rest, h, hs => by
    have hf := Func.reads f (ht f (.head _))
    have his := readItems_reads items fun f' hf' => ht f' (.tail _ hf')
    simp only [List.flatMap_cons, Item.tokens, Func.tokens, List.cons_append,
      List.append_assoc] at h
    take_pos h p
    obtain ⟨si, ⟨r, hr⟩, h₁, h₂, h₃⟩ := hf p _ (items.flatMap Item.tokens ++ rest)
      (by simpa only [Func.tokens, List.tail_cons, List.cons_append, List.append_assoc] using h)
      fun _ _ => trivial
    obtain ⟨sis, ⟨r', hr'⟩, h₄, h₅, h₆⟩ := his r rest h₃ hs
    rw [readItems.eq_1]
    simp only [true_and, String.reduceEq, ↓reduceIte, h₁, ok_bind, h₄]
    exact ⟨_, _, rfl, by simp [SItem.eraseList, Item.tree, h₂, h₅], h₆⟩

/-- The grammar step: on the tokens of a module, then `eof`, at any
positions, `readModule` gives the module's tree, up to positions, when each
type the module writes is written as a type and its location table is
within the limits. -/
theorem readModule_tokens {m : Module d}
    (ht : ∀ f ∈ m.funcs, ∀ t ∈ f.types, (tyAttr t).IsType) (hl : m.locs.InLimits)
    {ts : List Token} (h : ts.map (·.tok) = m.tokens ++ [.eof]) :
    ∃ s, readModule ts = .ok s ∧ s.erase = m.tree := by
  simp only [Module.tokens, List.append_assoc] at h
  obtain ⟨items, ⟨r, hr⟩, h₁, h₂, h₃⟩ := readItems_reads m.items
    (fun f hf => ht f (List.mem_map.mpr ⟨_, hf, rfl⟩)) ts _ h (by simp [LocTable.tokens])
  have h₃' : r.map (·.tok) = .word "locs" :: (m.locs.tokens.tail ++ [.eof]) := by
    simpa [LocTable.tokens] using h₃
  obtain ⟨q, r', rfl, -⟩ := map_tok_cons h₃'
  obtain ⟨locs, ⟨r₂, hr₂⟩, h₄, h₅, h₆⟩ := LocTable.reads m.locs hl _ [.eof] h₃ fun _ _ => trivial
  take_tok h₆
  rw [readModule.eq_1]
  simp only [h₁, ok_bind, h₄, expect_cons]
  exact ⟨_, rfl, by simp [SModule.erase, Module.tree, h₂, ← h₅]⟩

variable [DialectSignature d]

/-- The grammar step for a well-formed module: each type it writes is
written as a type, and its location table is within the limits. -/
theorem Module.WellFormed.readModule_tokens {m : Module d} (h : m.WellFormed) {ts : List Token}
    (hts : ts.map (·.tok) = m.tokens ++ [.eof]) :
    ∃ s, readModule ts = .ok s ∧ s.erase = m.tree :=
  Fir.readModule_tokens (fun f hf t ht => ((h.funcs f hf).types t ht).1) h.locs hts

/-- The first two steps of the parser read the printed text of a
well-formed module as the module's tree, up to positions. -/
theorem Module.WellFormed.read_print {m : Module d} (h : m.WellFormed) :
    ∃ ts s, lex m.print = .ok ts ∧ readModule ts = .ok s ∧ s.erase = m.tree := by
  obtain ⟨ts, h₁, h₂⟩ := h.lex_print
  obtain ⟨s, h₃, h₄⟩ := h.readModule_tokens h₂
  exact ⟨ts, s, h₁, h₃, h₄⟩

/-- The first two steps of the parser read the printed text of a valid
module of a dialect with lawful text as the module's tree. -/
theorem Module.Valid.read_print [DialectValidation d] [LawfulDialectText d] {m : Module d}
    (h : m.Valid) : ∃ ts s, lex m.print = .ok ts ∧ readModule ts = .ok s ∧ s.erase = m.tree :=
  (validIsWellFormed m h).read_print

end Fir
