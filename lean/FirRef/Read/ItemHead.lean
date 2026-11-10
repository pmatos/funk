import FirRef.Read.BlocksProof
import FirRef.Read.Dialects

/-!
An item's head, everything from its symbol through the `{` of its body, is
flat: `itemHeadC` reads it on a cursor, and `itemHeadS` is the same part of
the spec's `readItem`, from the spec's readers it calls. `U_readItem` and
`U_readItems_word` push `U` into the spec's readers of items, for the items
machine's proof.
-/

namespace FirRef

open Fir Fir.Text Cursor

/-- An item whose body is not read yet. -/
structure ItemHead where
  kind : String
  kindPos : TextPos
  name : String
  params : List SDef
  results : List (Attr × TextPos)
  attrs : List (Attr × TextPos)

/-- The item of a head and a body. -/
def ItemHead.item (h : ItemHead) (body : SBody) : SItem :=
  ⟨h.kind, h.kindPos, h.name, h.params, h.results, h.attrs, body⟩

/-- What `readItem` reads of an item's parameters. -/
def itemParamsS (ts : List Token) : Except ParseError (List SDef × List Token) :=
  match ts with
  | ⟨.rparen, _⟩ :: _ => pure ([], ts)
  | ts' => U (readDefs ts')

/-- What `readItem` reads of an item's results. -/
def itemResultsS (ts : List Token) : Except ParseError (List (Attr × TextPos) × List Token) :=
  match ts with
  | ⟨.arrow, _⟩ :: rest => do
    let (t, a) ← U (readType rest)
    let (more, b) ← U (readMore readType a)
    pure (t :: more, b)
  | ts' => pure ([], ts')

/-- What `readItem` reads before an item's body. -/
def itemHeadS (kind : String) (p : TextPos) (ts : List Token) :
    Except ParseError (ItemHead × List Token) :=
  match ts with
  | ⟨.sym name, _⟩ :: rest => do
    let ((), r₁) ← U (expect .lparen "( and the item's parameters" rest)
    let (params, r₂) ← itemParamsS r₁
    let ((), r₃) ← U (expect .rparen ")" r₂)
    let (results, r₄) ← itemResultsS r₃
    let (attrs, r₅) ← U (readAttrs r₄)
    let ((), r₆) ← U (expect .lbrace "{ and the item's body" r₅)
    pure (⟨kind, p, name, params, results, attrs⟩, r₆)
  | ts => fail ts "the item's symbol"

/-- What `readItem` reads of an item's body, after its `{`. -/
def itemBodyS (ts : List Token) : Except ParseError (SBody × List Token) :=
  match ts with
  | ⟨.word w, q⟩ :: tl => do
    let (ds, r) ← U (readDialects (⟨.word w, q⟩ :: tl))
    let (is, r') ← U (readItems false r)
    pure (SBody.items ds is, r')
  | ts' => do
    let (bs, r) ← U (readBlocks ts')
    pure (SBody.blocks bs, r)

/-- `U` of a bind of a spec reader `X`, when `U X` is `Y` and the rest
agrees on every result: the proof of `U_readItem` takes `readItem`'s
`match`es one at a time with it, as `bind_reads` does in the spec. -/
theorem U_bind_of {α β : Type} {P Q : List Token → Prop} {X : Except ParseError (α × Subtype P)}
    {K : α × Subtype P → Except ParseError (β × Subtype Q)} {Y : Except ParseError (α × List Token)}
    {K' : α × List Token → Except ParseError (β × List Token)} (hX : U X = Y)
    (hK : ∀ a r (hr : P r), U (K (a, ⟨r, hr⟩)) = K' (a, r)) : U (X >>= K) = Y >>= K' := by
  subst hX
  rcases X with e | ⟨a, r, hr⟩
  · rfl
  · exact hK a r hr

theorem U_readItem (kind : String) (p : TextPos) (ts : List Token) :
    U (readItem kind p ts) = (do
      let (hd, r₆) ← itemHeadS kind p ts
      let (body, r₇) ← itemBodyS r₆
      let ((), r₈) ← U (expect .rbrace "} to close the item's body" r₇)
      pure (hd.item body, r₈)) := by
  rw [readItem.eq_def]
  split
  · rename_i name q rest
    simp only [itemHeadS, bind_assoc]
    refine U_bind_of rfl ?_
    rintro ⟨⟩ r₁ h₁
    simp only
    refine U_bind_of (Y := itemParamsS r₁) ?_ ?_
    · split
      · rfl
      · rename_i hn
        unfold itemParamsS
        split
        · exact (hn _ _ _ rfl HEq.rfl).elim
        · rfl
    rintro ps r₂ h₂
    simp only
    refine U_bind_of rfl ?_
    rintro ⟨⟩ r₃ h₃
    simp only
    refine U_bind_of (Y := itemResultsS r₃) ?_ ?_
    · split
      · simp only [itemResultsS]
        refine U_bind_of rfl ?_
        rintro t a ha
        refine U_bind_of rfl ?_
        rintro more b hb
        rfl
      · rename_i hn
        unfold itemResultsS
        split
        · exact (hn _ _ _ rfl HEq.rfl).elim
        · rfl
    rintro rs r₄ h₄
    simp only
    refine U_bind_of rfl ?_
    rintro attrs r₅ h₅
    simp only
    refine U_bind_of rfl ?_
    rintro ⟨⟩ r₆ h₆
    simp only [pure_bind]
    refine U_bind_of (Y := itemBodyS r₆) ?_ ?_
    · split
      · simp only [itemBodyS]
        refine U_bind_of rfl ?_
        rintro ds r hr
        refine U_bind_of rfl ?_
        rintro is r' hr'
        rfl
      · rename_i hn
        unfold itemBodyS
        split
        · exact (hn _ _ _ _ rfl HEq.rfl).elim
        · refine U_bind_of rfl ?_
          rintro bs a ha
          rfl
    rintro body r₇ h₇
    simp only
    refine U_bind_of rfl ?_
    rintro ⟨⟩ r₈ h₈
    rfl
  · simp only [itemHeadS, U_fail, fail_bind]

theorem U_readItems_word (top : Bool) (w : String) (p : TextPos) (rest : List Token)
    (h : ¬(top = true ∧ w = "locs")) :
    U (readItems top (⟨.word w, p⟩ :: rest)) = (do
      let (i, r) ← U (readItem w p rest)
      let (is, r') ← U (readItems top r)
      pure (i :: is, r')) := by
  rw [readItems]
  simp only [h, ite_false]
  rcases readItem w p rest with e | ⟨i, r, hr⟩
  · rfl
  · simp only [okBind, U_ok]
    rcases readItems top r with e | ⟨is, r', hr'⟩ <;> rfl

end FirRef
