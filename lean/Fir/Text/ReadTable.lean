import Fir.Text.ReadDefs

/-!
# Reading the printed location table

Each location's tokens read back as the location, whatever follows them:
every kind of location ends with a token that its reader reads alone, a
number, a `)` or the word `unknown`. A source range reads back when its
lines and columns are below `2^32`, the limit that `readNat` checks and
that `LocTable.InLimits` gives. The table's entries read back before its
`}`, and the table before any token.
-/

namespace Fir.Text

/-- Takes the first token off `h : ts.map (·.tok) = t :: rest`: `ts` becomes
`⟨t, p⟩ :: ts'`, and `h` says that `ts'.map (·.tok) = rest`. -/
local macro "take_tok " h:ident : tactic => `(tactic| (
  (try dsimp only at $h:ident)
  replace $h:ident := map_tok_cons $h
  obtain ⟨_, _, he, $h:ident⟩ := $h
  subst he))

/-- `readNat` reads a number below `2^32`. -/
theorem readNat_cons (what : String) {n : Nat} (hn : n < Location.limit) (p : TextPos)
    (ts : List Token) : readNat what (⟨.int n, p⟩ :: ts) = .ok (n, ⟨ts, Nat.le_succ _⟩) := by
  rw [show ((n : Int)) = Int.ofNat n from rfl, readNat.eq_1]
  simp only [hn, ↓reduceIte]

/-- `readLocRef` reads a location reference. -/
theorem readLocRef_cons (r : LocRef) (p : TextPos) (ts : List Token) :
    readLocRef (⟨.locRef r, p⟩ :: ts) = .ok (r, ⟨ts, Nat.le_succ _⟩) := by
  rw [readLocRef.eq_1]

/-- `readLocRef` reads a location reference, for `readMore`. -/
theorem readLocRef_reads (r : LocRef) : Reads readLocRef id r [.locRef r] (· ≠ .lparen) := by
  intro ts rest h _
  simp only [List.cons_append, List.nil_append] at h
  take_tok h
  rw [readLocRef_cons]
  exact ⟨_, _, rfl, rfl, h⟩

/-- `readLocation` reads a location's tokens as the location, when its
lines and columns are below `2^32`. -/
theorem Location.reads (l : Location) (hl : ∀ n ∈ l.numbers, n < Location.limit) :
    Reads readLocation id l l.tokens (fun _ => True) := by
  intro ts rest h _
  cases l with
  | unknown =>
    simp only [Location.tokens, List.cons_append, List.nil_append] at h
    take_tok h
    rw [readLocation.eq_2]
    exact ⟨_, _, rfl, rfl, h⟩
  | range f l₁ c₁ l₂ c₂ =>
    simp only [Location.numbers, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hl
    simp only [Location.tokens, List.cons_append, List.nil_append] at h
    iterate 9 take_tok h
    rw [readLocation.eq_1]
    simp only [readRange, keyword, expect_cons, readNat_cons _ hl.1, readNat_cons _ hl.2.1,
      readNat_cons _ hl.2.2.1, readNat_cons _ hl.2.2.2, ok_bind, pure_bind, After.then,
      After.next]
    exact ⟨_, _, rfl, rfl, h⟩
  | name n =>
    simp only [Location.tokens, List.cons_append, List.nil_append] at h
    iterate 4 take_tok h
    rw [readLocation.eq_3 _ _ _ (by decide)]
    simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, ↓reduceIte, expect_cons,
      ok_bind, readLocArgs.eq_1, pure_bind, After.then, After.next]
    exact ⟨_, _, rfl, rfl, h⟩
  | callsite callee caller =>
    simp only [Location.tokens, List.cons_append, List.nil_append] at h
    iterate 6 take_tok h
    rw [readLocation.eq_3 _ _ _ (by decide)]
    simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true, ↓reduceIte,
      expect_cons, ok_bind, readLocArgs.eq_3, readLocRef_cons, keyword, pure_bind, After.then,
      After.next]
    exact ⟨_, _, rfl, rfl, h⟩
  | derived src =>
    simp only [Location.tokens, List.cons_append, List.nil_append] at h
    iterate 4 take_tok h
    rw [readLocation.eq_3 _ _ _ (by decide)]
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_true, ↓reduceIte,
      expect_cons, ok_bind, readLocArgs.eq_6 "derived" _ (by decide) (by decide) (by decide),
      readLocRef_cons, pure_bind, After.then, After.next]
    exact ⟨_, _, rfl, rfl, h⟩
  | fused locs =>
    simp only [Location.tokens, List.cons_append, List.append_assoc] at h
    take_tok h
    take_tok h
    rw [readLocation.eq_3 _ _ _ (by decide)]
    simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true, ↓reduceIte,
      expect_cons, ok_bind]
    cases locs with
    | nil =>
      simp only [List.map_nil, List.intercalate_nil, List.nil_append] at h
      take_tok h
      simp only [readLocArgs.eq_4, pure_bind, After.here, After.then, After.next, expect_cons,
        ok_bind]
      exact ⟨_, _, rfl, rfl, h⟩
    | cons r rs =>
      rw [List.map_cons, intercalate_cons, flatMap_comma_map] at h
      simp only [List.cons_append, List.nil_append] at h
      take_tok h
      obtain ⟨rs', ⟨r', hr'⟩, h₁, h₂, h₃⟩ := Reads.more (stop := (· ≠ .lparen)) (by decide)
        (stop' := (· = .rparen)) (fun t ht => by subst ht; decide)
        (fun y _ => readLocRef_reads y) _ _ h (by simp)
      take_tok h₃
      rw [readLocArgs.eq_5 _ fun _ _ he => by simp at he]
      simp only [readLocRef_cons, ok_bind, h₁, pure_bind, After.then, After.next, expect_cons]
      exact ⟨_, _, rfl, by simpa using h₂, h₃⟩

/-- `readLocEntries` reads the entries of a location table within the
limits, before a `}`. -/
theorem readLocEntries_reads (t : LocTable) (hl : t.InLimits) :
    Reads readLocEntries id t (t.flatMap fun (r, l) => .locRef r :: .eq :: l.tokens)
      (· = .rbrace) := by
  induction t with
  | nil =>
    intro ts rest h hs
    simp only [List.flatMap_nil, List.nil_append] at h
    rw [readLocEntries.eq_2 _ fun r p rest' he => by
      subst he
      exact absurd (hs (.locRef r) (by rw [← h]; rfl)) (by simp)]
    exact ⟨_, _, rfl, rfl, h⟩
  | cons e t ih =>
    intro ts rest h hs
    obtain ⟨r, l⟩ := e
    have ih := ih fun e he => hl e (.tail _ he)
    simp only [List.flatMap_cons, List.cons_append, List.append_assoc] at h
    take_tok h
    take_tok h
    obtain ⟨l', ⟨r₁, hr₁⟩, h₁, h₂, h₃⟩ := Location.reads l (hl _ (.head _)).2 _ _ h fun _ _ => trivial
    obtain ⟨t', ⟨r₂, hr₂⟩, h₄, h₅, h₆⟩ := ih r₁ rest h₃ hs
    rw [readLocEntries.eq_1]
    simp only [expect_cons, ok_bind, h₁, h₄]
    exact ⟨_, _, rfl, by simp_all, h₆⟩

/-- `readLocs` reads a location table within the limits. -/
theorem LocTable.reads (t : LocTable) (hl : t.InLimits) :
    Reads readLocs id t t.tokens (fun _ => True) := by
  intro ts rest h _
  simp only [LocTable.tokens, List.cons_append, List.append_assoc] at h
  take_tok h
  take_tok h
  obtain ⟨t', ⟨r, hr⟩, h₁, h₂, h₃⟩ := readLocEntries_reads t hl _ _ h (by simp)
  take_tok h₃
  simp only [readLocs, keyword, expect_cons, ok_bind, h₁, After.then]
  exact ⟨_, _, rfl, h₂, h₃⟩

end Fir.Text
