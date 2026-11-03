import Fir.Text.ReadLocs
import FirRef.Except

/-!
`fir-ref` reads tokens with the readers of `FirRef.Read`, not with the
spec's. The spec's readers recurse once per level of nesting and once per
element of most lists, without a tail call, so a deep or long text
overflows the stack. The readers here are loops whose every call to
themselves is a tail call, and they keep what is left to do on an explicit
stack of frames.

They take their tokens from a cursor: a list of tokens, or a lexer that
reads each token from the text when a reader asks for it, so that no list
of tokens exists. `Cursor.view` is the tokens that a cursor holds, as a
list. Proofs and measures of termination use it, and code never calls it.
Each reader is proved to give what the spec's reader gives on the view of
its cursor, errors included: the theorems compare `V` of the one with `U`
of the other, which forget how each holds the tokens after what it read.
-/

namespace FirRef

open Fir Fir.Text

/-- A source of tokens that the readers take one at a time. -/
class Cursor (σ : Type) where
  /-- The next token and the cursor after it, or `none` when no token is
  left. -/
  uncons : σ → Option (Token × σ)
  /-- The tokens left, as a list. -/
  view : σ → List Token
  /-- The view lists the tokens that `uncons` gives, in order. -/
  view_uncons (s : σ) : view s = match uncons s with
    | none => []
    | some (t, s') => t :: view s'

namespace Cursor

variable {σ : Type} [Cursor σ]

theorem view_of_uncons {s s' : σ} {t : Token} (h : uncons s = some (t, s')) :
    view s = t :: view s' := by
  rw [view_uncons s, h]

theorem view_of_uncons_none {s : σ} (h : uncons s = none) : view s = [] := by
  rw [view_uncons s, h]

theorem length_lt {s s' : σ} {t : Token} (h : uncons s = some (t, s')) :
    (view s').length < (view s).length := by
  rw [view_of_uncons h]
  simp

end Cursor

/-- A list of tokens is a cursor that holds them. -/
instance : Cursor (List Token) where
  uncons
    | [] => none
    | t :: ts => some (t, ts)
  view ts := ts
  view_uncons ts := by cases ts <;> rfl

open Cursor

/-- What a spec reader returns, with the tokens after what it read as a
plain list. -/
def U {α : Type} {P : List Token → Prop} (x : Except ParseError (α × Subtype P)) :
    Except ParseError (α × List Token) :=
  x.map fun p => (p.1, p.2.1)

/-- What a reader of a cursor returns, with the tokens after what it read
as a list. -/
def V {σ α : Type} [Cursor σ] (x : Except ParseError (α × σ)) :
    Except ParseError (α × List Token) :=
  x.map fun p => (p.1, view p.2)

variable {σ : Type} [Cursor σ] {α : Type}

@[simp] theorem U_ok {P : List Token → Prop} (a : α) (r : Subtype P) :
    U (.ok (a, r)) = .ok (a, r.1) := rfl

@[simp] theorem U_error {P : List Token → Prop} (e : ParseError) :
    U (.error e : Except ParseError (α × Subtype P)) = .error e := rfl

@[simp] theorem V_ok (a : α) (s : σ) : V (.ok (a, s)) = .ok (a, view s) := rfl

@[simp] theorem V_error (e : ParseError) : V (.error e : Except ParseError (α × σ)) = .error e :=
  rfl

@[simp] theorem U_fail {P : List Token → Prop} (ts : List Token) (expected : String) :
    U (fail ts expected : Except ParseError (α × Subtype P)) = fail ts expected := by
  cases ts <;> rfl

@[simp] theorem V_fail (ts : List Token) (expected : String) :
    V (fail ts expected : Except ParseError (α × σ)) = fail ts expected := by
  cases ts <;> rfl

/-- A spec reader leaves no more tokens than it was given. -/
theorem length_le_of_U {ts : List Token} {x : Read α ts} {a : α} {r : List Token}
    (h : U x = .ok (a, r)) : r.length ≤ ts.length := by
  match x, h with
  | .ok (_, ⟨_, hr⟩), h =>
    simp only [U_ok, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ hr

/-- A reader that agrees with a spec reader leaves no more tokens than it
was given. -/
theorem length_le {s s' : σ} {ts : List Token} {x : Except ParseError (α × σ)} {y : Read α ts}
    {a : α} (hxy : V x = U y) (hts : view s = ts) (h : x = .ok (a, s')) :
    (view s').length ≤ (view s).length := by
  subst h hts
  exact length_le_of_U (hxy.symm.trans (V_ok a s'))

/-- A spec reader that reads at least one token leaves fewer than it was
given. -/
theorem length_lt_of_U {ts : List Token} {x : Read1 α ts} {a : α} {r : List Token}
    (h : U x = .ok (a, r)) : r.length < ts.length := by
  match x, h with
  | .ok (_, ⟨_, hr⟩), h =>
    simp only [U_ok, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ hr

/-- A reader that agrees with a spec reader that reads at least one token
leaves fewer tokens than it was given. -/
theorem length_lt' {s s' : σ} {ts : List Token} {x : Except ParseError (α × σ)} {y : Read1 α ts}
    {a : α} (hxy : V x = U y) (hts : view s = ts) (h : x = .ok (a, s')) :
    (view s').length < (view s).length := by
  subst h hts
  exact length_lt_of_U (hxy.symm.trans (V_ok a s'))

@[simp] theorem After.here_val (ts : List Token) : (After.here ts).1 = ts := rfl

@[simp] theorem After.next_val {t : Token} {ts : List Token} (a : After ts) :
    (After.next (t := t) a).1 = a.1 := rfl

@[simp] theorem After.then_val {ts : List Token} (a : After ts) (b : After a.1) :
    (a.then b).1 = b.1 := rfl

/-- `U` moves into a bind: the spec's readers' `do` blocks become chains of
spec readers, each with `U` applied to the last step. -/
theorem U_bind {β : Type} {P Q : List Token → Prop} (x : Except ParseError (α × Subtype P))
    (f : α × Subtype P → Except ParseError (β × Subtype Q)) :
    U (x >>= f) = x >>= fun a => U (f a) := by
  cases x <;> rfl

theorem bind_U {γ : Type} {P : List Token → Prop} (x : Except ParseError (α × Subtype P))
    (g : α × List Token → Except ParseError γ) :
    U x >>= g = x >>= fun a => g (a.1, a.2.1) := by
  cases x <;> rfl

theorem U_pure {P : List Token → Prop} (a : α) (r : Subtype P) :
    U (pure (a, r) : Except ParseError (α × Subtype P)) = pure (a, r.1) := rfl

theorem U_bind_pure {P Q : List Token → Prop} (x : Except ParseError (α × Subtype P))
    (h : ∀ a : α × Subtype P, Q a.2.1) :
    U (x >>= fun a => pure (a.1, ⟨a.2.1, h a⟩)) = U x := by
  cases x <;> rfl

theorem fail_bind {β : Type} (ts : List Token) (expected : String)
    (k : α → Except ParseError β) :
    ((fail ts expected : Except ParseError α) >>= k) = fail ts expected := by
  cases ts <;> rfl

/-- Moves `U` into the binds of a spec reader's `do` block. -/
macro "U_norm" : tactic => `(tactic| simp only [U_bind, bind_U, U_pure, bind_assoc, pure_bind])

/-- A reader that agrees with a spec reader fails with the same error, or
reads the same value and leaves a cursor whose view is the same tokens. -/
theorem agree {P : List Token → Prop} {x : Except ParseError (α × σ)}
    {y : Except ParseError (α × Subtype P)} (h : V x = U y) :
    (∃ e, x = .error e ∧ y = .error e) ∨
      (∃ a s r hr, x = .ok (a, s) ∧ y = .ok (a, ⟨r, hr⟩) ∧ view s = r) := by
  rcases x with e | ⟨a, s⟩ <;> rcases y with e' | ⟨a', r, hr⟩ <;>
    simp only [V_ok, V_error, U_ok, U_error, Except.error.injEq, Except.ok.injEq,
      Prod.mk.injEq, reduceCtorEq] at h
  · exact .inl ⟨e, rfl, by rw [h]⟩
  · obtain ⟨rfl, rfl⟩ := h
    exact .inr ⟨a, s, view s, hr, rfl, rfl, rfl⟩

/-- `agree`, when the reader's value is `f` of the spec reader's. -/
theorem agree_map {β : Type} {P : List Token → Prop} {f : α → β} {x : Except ParseError (β × σ)}
    {y : Except ParseError (α × Subtype P)} (h : V x = (U y).map fun p => (f p.1, p.2)) :
    (∃ e, x = .error e ∧ y = .error e) ∨
      (∃ a s r hr, x = .ok (f a, s) ∧ y = .ok (a, ⟨r, hr⟩) ∧ view s = r) := by
  rcases x with e | ⟨b, s⟩ <;> rcases y with e' | ⟨a, r, hr⟩ <;>
    simp only [V_ok, V_error, U_ok, U_error, okExceptMap, errorExceptMap, Except.error.injEq,
      Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
  · exact .inl ⟨e, rfl, by rw [h]⟩
  · obtain ⟨rfl, rfl⟩ := h
    exact .inr ⟨a, s, view s, hr, rfl, rfl, rfl⟩

/-- When the next token of a cursor is not `tok`, its view does not start
with `tok`. -/
theorem not_head {s : σ} {tok : Tok} (h : ∀ p s', uncons s = some (⟨tok, p⟩, s') → False) :
    ∀ p rest, view s ≠ ⟨tok, p⟩ :: rest := by
  intro p rest he
  cases hs : uncons s with
  | none => rw [view_of_uncons_none hs] at he; cases he
  | some v =>
    obtain ⟨t, s'⟩ := v
    rw [view_of_uncons hs] at he
    cases he
    exact h p s' hs

/-- One step of a proof that a reader on a cursor agrees with a spec
reader: `h` says that the step's reader agrees with the spec's; on an
error both fail, and otherwise the value is `a` and the cursor after it
`s`, whose view replaces the spec's list of tokens after the step. -/
syntax "agree_step " term " with " Lean.Parser.Tactic.rcasesPatLo Lean.Parser.Tactic.rcasesPatLo : tactic

macro_rules
  | `(tactic| agree_step $h with $a $s) => `(tactic| (
      rcases agree $h with ⟨_, hx, hy⟩ | ⟨$a, $s, _, _, hx, hy, hv⟩
      · rw [hx, hy]; rfl
      rw [hx, hy]
      subst hv
      simp only [U_ok, okBind, pure_bind]))

/-! # Reading one token -/

/-- `fail` on the tokens of a cursor. -/
def failC (s : σ) (expected : String) : Except ParseError α :=
  match uncons s with
  | some (t, _) => fail [t] expected
  | none => fail [] expected

theorem failC_eq (s : σ) (expected : String) :
    (failC s expected : Except ParseError α) = fail (view s) expected := by
  unfold failC
  split
  · rename_i h
    rw [view_of_uncons h]
    rfl
  · rename_i h
    rw [view_of_uncons_none h]

/-- `expect`, on a cursor. -/
def expectC (tok : Tok) (expected : String) (s : σ) : Except ParseError (Unit × σ) :=
  match uncons s with
  | some (t, s') => if t.tok = tok then .ok ((), s') else fail [t] expected
  | none => fail [] expected

theorem expectC_eq (tok : Tok) (expected : String) (s : σ) :
    V (expectC tok expected s) = U (expect tok expected (view s)) := by
  unfold expectC
  split
  · rename_i t s' h
    rw [view_of_uncons h]
    simp only [expect]
    split <;> simp_all <;> rfl
  · rename_i h
    rw [view_of_uncons_none h]
    simp [expect]

theorem expectC_lt {tok : Tok} {expected : String} {s s' : σ} {u : Unit}
    (h : expectC tok expected s = .ok (u, s')) : (view s').length < (view s).length := by
  unfold expectC at h
  split at h
  · rename_i t s'' hs
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact h.2 ▸ length_lt hs
    · cases h
  · cases h

/-- `keyword`, on a cursor. -/
def keywordC (kw : String) (s : σ) : Except ParseError (Unit × σ) :=
  expectC (.word kw) ("`" ++ kw ++ "`") s

theorem keywordC_eq (kw : String) (s : σ) : V (keywordC kw s) = U (keyword kw (view s)) :=
  expectC_eq _ _ _

/-- `readOpLoc`, on what `uncons s` gave, so that a reader that looked at
the next token reads it without taking it again. -/
def opLocOf (s : σ) : Option (Token × σ) → Except ParseError (LocRef × σ)
  | some (⟨.locRef r, _⟩, s') => .ok (r, s')
  | _ => failC s "the op's location reference, such as @0"

/-- `readOpLoc`, on a cursor. -/
def readOpLocC (s : σ) : Except ParseError (LocRef × σ) := opLocOf s (uncons s)

theorem readOpLocC_eq (s : σ) : V (readOpLocC s) = U (readOpLoc (view s)) := by
  unfold readOpLocC opLocOf
  split
  · rename_i r p s' h
    rw [view_of_uncons h]
    rfl
  · rename_i hn
    rw [failC_eq, V_fail]
    cases h : uncons s with
    | none => rw [view_of_uncons_none h]; rfl
    | some v =>
      obtain ⟨⟨t, p⟩, s'⟩ := v
      rw [view_of_uncons h]
      cases t <;> first | rfl | exact absurd h (hn _ _ _)

/-- `readLocRef`, on a cursor. -/
def readLocRefC (s : σ) : Except ParseError (LocRef × σ) :=
  match uncons s with
  | some (⟨.locRef r, _⟩, s') => .ok (r, s')
  | _ => failC s "a location reference, such as @0"

theorem readLocRefC_eq (s : σ) : V (readLocRefC s) = U (readLocRef (view s)) := by
  unfold readLocRefC
  split
  · rename_i r p s' h
    rw [view_of_uncons h]
    rfl
  · rename_i hn
    rw [failC_eq, V_fail]
    cases h : uncons s with
    | none => rw [view_of_uncons_none h]; rfl
    | some v =>
      obtain ⟨⟨t, p⟩, s'⟩ := v
      rw [view_of_uncons h]
      cases t <;> first | rfl | exact absurd h (hn _ _ _)

end FirRef
