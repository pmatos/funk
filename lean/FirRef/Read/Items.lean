import FirRef.Read.ItemHeadC

/-!
Items hold items to any depth: `module @a() {module @b() {…}}`. `itemsLoop`
reads items with an explicit stack of frames: a frame of items, the items
read so far last first, and below each nested one a frame for the item
whose body they are, with the dialect set that starts that body. An item whose body is blocks is read whole, by the
blocks machine. Every call to itself is a tail call. `iRun` says what a
stack means by the spec's readers, and `itemsLoop_eq` proves that the loop
computes it, errors included.
-/

namespace FirRef

open Fir Fir.Text Cursor

/-- What is left to read of items. -/
inductive IFrame where
  /-- Items, those read last first; at the top of the module when `top`. -/
  | items (top : Bool) (done : List SItem)
  /-- The item with this head, whose body is this dialect set and the items
  above. -/
  | item (head : ItemHead) (dialects : List Name)

variable {σ : Type} [Cursor σ]

/-- Whether the next token is the word `locs`. It looks at the token and
does not take it. -/
def atLocs (s : σ) : Bool :=
  match uncons s with
  | some (⟨.word w, _⟩, _) => w == "locs"
  | _ => false

/-- The kind of the next item and the cursor after it, if an item follows:
a word, but not `locs` at the top of the module. -/
def nextItem (top : Bool) (s : σ) : Option (String × TextPos × σ) :=
  if top && atLocs s then none
  else
    match uncons s with
    | some (⟨.word w, p⟩, s₁) => some (w, p, s₁)
    | _ => none

theorem nextItem_some {top : Bool} {s s₁ : σ} {w : String} {p : TextPos}
    (h : nextItem top s = some (w, p, s₁)) :
    uncons s = some (⟨.word w, p⟩, s₁) ∧ ¬(top = true ∧ w = "locs") := by
  unfold nextItem at h
  split at h
  · cases h
  · rename_i ht
    split at h
    · rename_i w' p' s' hs
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨hs, ?_⟩
      rintro ⟨rfl, rfl⟩
      apply ht
      simp [atLocs, hs]
    · cases h

theorem U_readItems_none {top : Bool} {s : σ} (h : nextItem top s = none) :
    U (readItems top (view s)) = .ok ([], view s) := by
  unfold nextItem at h
  split at h
  · rename_i ht
    simp only [Bool.and_eq_true] at ht
    obtain ⟨rfl, hl⟩ := ht
    unfold atLocs at hl
    split at hl
    · rename_i w p s₁ hs
      simp only [beq_iff_eq] at hl
      subst hl
      rw [view_of_uncons hs, readItems]
      simp
    · cases hl
  · split at h
    · cases h
    · rename_i hn
      rw [readItems]
      · rfl
      · intro w p rest he
        exact not_head (hn w) p rest he

/-- `readBlocks`, on a cursor, with no stack per level. -/
def readBlocksC (s : σ) : Except ParseError (List SBlock × σ) := blocksLoop s [.blocks []]

theorem readBlocksC_eq (s : σ) : V (readBlocksC s) = U (readBlocks (view s)) := by
  rw [readBlocksC, blocksLoop_eq]
  simp only [bRun, bFinish]
  rcases U (readBlocks (view s)) with e | ⟨bs, r⟩ <;> simp

theorem readBlocksC_le {s s' : σ} {bs : List SBlock} (h : readBlocksC s = .ok (bs, s')) :
    (view s').length ≤ (view s).length :=
  length_le (readBlocksC_eq s) rfl h

/-- Reads the items that the frames `fs` leave. -/
def itemsLoop (s : σ) (fs : List IFrame) : Except ParseError (List SItem × σ) :=
  match fs with
  | .items top done :: fs =>
    match _h : nextItem top s with
    | some (w, p, s₁) =>
      match _hh : itemHeadC w p s₁ with
      | .ok (hd, s₂) =>
        match _hw : uncons s₂ with
        | some (⟨.word _, _⟩, _) =>
          match _hd : readDialectsC s₂ with
          | .ok (ds, s₃) => itemsLoop s₃ (.items false [] :: .item hd ds :: .items top done :: fs)
          | .error e => .error e
        | _ =>
          match _hb : readBlocksC s₂ with
          | .ok (bs, s₃) =>
            match _he : expectC .rbrace "} to close the item's body" s₃ with
            | .ok ((), s₄) => itemsLoop s₄ (.items top (hd.item (.blocks bs) :: done) :: fs)
            | .error e => .error e
          | .error e => .error e
      | .error e => .error e
    | none =>
      match fs with
      | [] => .ok (done.reverse, s)
      | .item hd ds :: .items top' done' :: fs =>
        match _he : expectC .rbrace "} to close the item's body" s with
        | .ok ((), s₁) =>
          itemsLoop s₁ (.items top' (hd.item (.items ds done.reverse) :: done') :: fs)
        | .error e => .error e
      | _ => .ok ([], s)
  | _ => .ok ([], s)
termination_by (view s).length
decreasing_by
  · have := readDialectsC_le _hd
    have := itemHeadC_lt _hh
    have := length_lt (nextItem_some _h).1
    omega
  · have := expectC_lt _he
    have := readBlocksC_le _hb
    have := itemHeadC_lt _hh
    have := length_lt (nextItem_some _h).1
    omega
  · exact expectC_lt _he

/-- Hands the items `is`, read in full, to the frames `fs`, which read on by
the spec's readers. -/
def iFinish : List SItem → List Token → List IFrame →
    Except ParseError (List SItem × List Token)
  | is, ts, [] => .ok (is, ts)
  | is, ts, .item hd ds :: .items top done :: fs => do
    let ((), r₁) ← U (expect .rbrace "} to close the item's body" ts)
    let (more, r₂) ← U (readItems top r₁)
    iFinish ((hd.item (.items ds is) :: done).reverse ++ more) r₂ fs
  | _, ts, _ => .ok ([], ts)

/-- What `itemsLoop` computes from the frames `fs`, by the spec's
readers. -/
def iRun (ts : List Token) : List IFrame → Except ParseError (List SItem × List Token)
  | .items top done :: fs => do
    let (is, r) ← U (readItems top ts)
    iFinish (done.reverse ++ is) r fs
  | _ => .ok ([], ts)

end FirRef
