import FirRef.Read.ItemsProof
import FirRef.Read.Locs

/-!
`fir-ref` reads a module's tokens with `FirRef.readModule`, not with the
spec's `Text.readModule`. `readModuleC` reads a module from a cursor: its
items with the items machine, then its location table, whose entries
`readLocEntriesC` reads with an accumulator. `readModuleC_eq` proves it
equal to the spec's reader on the cursor's tokens, errors included, and
`@[csimp]` makes Lean compile every later call of `Text.readModule` as a
call of `readModule`, the reader on a list of tokens.
-/

namespace FirRef

open Fir Fir.Text Cursor

variable {σ : Type} [Cursor σ]

/-- `readLocEntries`, on a cursor: the entries read so far are `acc`, last
first. -/
def readLocEntriesC (s : σ) (acc : LocTable) : Except ParseError (LocTable × σ) :=
  match _h : uncons s with
  | some (⟨.locRef r, _⟩, s₁) =>
    match _he : expectC .eq "= after the location reference" s₁ with
    | .ok ((), s₂) =>
      match _hl : readLocationC s₂ with
      | .ok (l, s₃) => readLocEntriesC s₃ ((r, l) :: acc)
      | .error e => .error e
    | .error e => .error e
  | _ => .ok (acc.reverse, s)
termination_by (view s).length
decreasing_by
  have := readLocationC_le _hl
  have := expectC_lt _he
  have := length_lt _h
  omega

theorem readLocEntriesC_eq (s : σ) (acc : LocTable) :
    V (readLocEntriesC s acc) =
      (U (readLocEntries (view s))).map fun (es, r) => (acc.reverse ++ es, r) := by
  fun_induction readLocEntriesC s acc with
  | case1 s acc r p s₁ h s₂ he l s₃ hl ih =>
    rw [ih, view_of_uncons h, readLocEntries]
    rcases agree (expectC_eq .eq "= after the location reference" s₁) with
      ⟨e, hx, hy⟩ | ⟨⟨⟩, s₂', r₂, hr₂, hx, hy, hv⟩
    · rw [he] at hx; cases hx
    · rw [he] at hx
      cases hx
      rw [hy]
      subst hv
      simp only [okBind]
      rcases agree (readLocationC_eq s₂) with
        ⟨e, hx', hy'⟩ | ⟨l', s₃', r₃, hr₃, hx', hy', hv'⟩
      · rw [hl] at hx'; cases hx'
      · rw [hl] at hx'
        cases hx'
        rw [hy']
        subst hv'
        simp only [okBind]
        rcases readLocEntries (view s₃) with e | ⟨es, r₄, hr₄⟩ <;> simp
  | case2 s acc r p s₁ h s₂ he e hl =>
    rw [view_of_uncons h, readLocEntries]
    rcases agree (expectC_eq .eq "= after the location reference" s₁) with
      ⟨e', hx, hy⟩ | ⟨⟨⟩, s₂', r₂, hr₂, hx, hy, hv⟩
    · rw [he] at hx; cases hx
    · rw [he] at hx
      cases hx
      rw [hy]
      subst hv
      simp only [okBind]
      rcases agree (readLocationC_eq s₂) with
        ⟨e', hx', hy'⟩ | ⟨l', s₃', r₃, hr₃, hx', hy', hv'⟩
      · rw [hl] at hx'
        cases hx'
        rw [hy']
        rfl
      · rw [hl] at hx'; cases hx'
  | case3 s acc r p s₁ h e he =>
    rw [view_of_uncons h, readLocEntries]
    rcases agree (expectC_eq .eq "= after the location reference" s₁) with
      ⟨e', hx, hy⟩ | ⟨⟨⟩, s₂', r₂, hr₂, hx, hy, hv⟩
    · rw [he] at hx
      cases hx
      rw [hy]
      rfl
    · rw [he] at hx; cases hx
  | case4 s acc hn =>
    rw [readLocEntries]
    · simp
    · intro r p rest he
      exact not_head (hn r) p rest he

/-- `readLocs`, on a cursor. -/
def readLocsC (s : σ) : Except ParseError (LocTable × σ) := do
  let ((), s₁) ← keywordC "locs" s
  let ((), s₂) ← expectC .lbrace "{ to open the location table" s₁
  let (es, s₃) ← readLocEntriesC s₂ []
  let ((), s₄) ← expectC .rbrace "an entry, such as `@0 = unknown`, or }" s₃
  pure (es, s₄)

theorem readLocsC_eq (s : σ) : V (readLocsC s) = U (readLocs (view s)) := by
  unfold readLocsC readLocs
  agree_step (keywordC_eq "locs" s) with ⟨⟩ s₁
  agree_step (expectC_eq .lbrace "{ to open the location table" s₁) with ⟨⟩ s₂
  rcases agree_map (f := fun q => ([].reverse ++ q)) (readLocEntriesC_eq s₂ []) with
    ⟨e, hx, hy⟩ | ⟨es, s₃, r, hr, hx, hy, hv⟩
  · rw [hx, hy]; rfl
  · rw [hx, hy]
    subst hv
    simp only [okBind, List.reverse_nil, List.nil_append]
    agree_step (expectC_eq .rbrace "an entry, such as `@0 = unknown`, or }" s₃) with ⟨⟩ s₄
    rfl

/-- `readModule`, on a cursor, with no stack per level and none per
element of a list. -/
def readModuleC (s : σ) : Except ParseError SModule :=
  match readItemsC s with
  | .ok (items, s₁) =>
    match uncons s₁ with
    | some (⟨.word "locs", _⟩, _) =>
      match readLocsC s₁ with
      | .ok (locs, s₂) =>
        match expectC .eof "the end of the text after the location table" s₂ with
        | .ok _ => .ok ⟨items, locs⟩
        | .error e => .error e
      | .error e => .error e
    | _ => failC s₁ "an item or the location table, `locs { ... }`"
  | .error e => .error e

theorem readModuleC_eq (s : σ) : readModuleC s = Text.readModule (view s) := by
  unfold readModuleC Text.readModule
  rcases agree (readItemsC_eq s) with ⟨e, hx, hy⟩ | ⟨items, s₁, r, hr, hx, hy, hv⟩
  · rw [hx, hy]; rfl
  · rw [hx, hy]
    subst hv
    simp only [okBind]
    split
    · rename_i p s₂ h
      rw [view_of_uncons h]
      simp only
      rw [← view_of_uncons h]
      rcases agree (readLocsC_eq s₁) with ⟨e, hx', hy'⟩ | ⟨locs, s₃, r', hr', hx', hy', hv'⟩
      · rw [hx', hy']; rfl
      · rw [hx', hy']
        subst hv'
        simp only [okBind]
        rcases agree (expectC_eq .eof "the end of the text after the location table" s₃) with
          ⟨e, hx'', hy''⟩ | ⟨⟨⟩, s₄, r'', hr'', hx'', hy'', hv''⟩
        · rw [hx'', hy'']; rfl
        · rw [hx'', hy'']; rfl
    · rename_i hn
      rw [failC_eq]
      split
      · rename_i p rest he
        exact absurd he (not_head (hn) p rest)
      · rfl

/-- The spec's `readModule`, on a list of tokens, with no stack per level
and none per element of a list. -/
def readModule (ts : List Token) : Except ParseError SModule := readModuleC ts

/-- `readModule` reads as the spec's reader does, errors included, so
`fir-ref` runs it in place of `Text.readModule`. -/
@[csimp] theorem readModule_eq_readModule : @Text.readModule = @readModule := by
  funext ts
  exact (readModuleC_eq ts).symm

end FirRef
