import Fir.Text.LexAccepted
import Fir.Text.ReadLocs
import Fir.Text.RoundTrip

/-!
# Trees that can be written

The grammar step reads tokens into a syntax tree. On tokens that can be
written, the tree it gives can be written too, part by part:

* a successor's label, and each value it passes, is a name, and each
  number of a location is below 2³²;
* a definition's value is a name, and its type is written as a type;
* an op's results can be written, its name is a word, its attributes and
  successors can be written, its regions can be written and its location
  reference is below 2³²; a block's label is a name, and its arguments
  and ops can be written;
* an item's parameters can be written, its result types are written as
  types, its attributes can be written, and the blocks of its body can be
  written; a module's dialect set
  names words, its items can be written, and each number of its location
  table is below 2³².

An op's operands are not in this list: decoding finds each of them among
the definitions of its function, whose names are names. An item's kind is
not in it either: decoding accepts only `func`, `module` and a word of a
dialect, which a word token gives. An item of a dialect's kind keeps its
attributes, so they are in it. A `func` whose body is a list of items is rejected
unless that list is empty, so nothing is asked of the items of a body.

Each reader takes what it needs from the tokens it reads. A name comes from
a value or a label token, a word from a word token, a reference from a
location reference token, a float literal from a float literal token, and
the lexer's step says that each of those tokens can be written. A reader gives a property on some tokens when, if
they can be written, what it reads has the property and the tokens it
leaves can be written. The tokens that a reader leaves are a suffix of the
tokens it was given, but a reader's definition records only that there are
no more of them, so each lemma shows that they can be written.
-/

namespace Fir

/-- A successor can be written: its label and the values it passes are
names. -/
def Succ.Writable (s : Succ) : Prop := isName s.label ∧ ∀ a ∈ s.args, isName a

/-- Every number of a location is below `2^32`. -/
def Location.InLimits (l : Location) : Prop := ∀ n ∈ l.numbers, n < Location.limit

end Fir

namespace Fir.Text

/-- A definition as read can be written: its value's name is a name, and its
type is written as a type. -/
def SDef.Writable (x : SDef) : Prop := isName x.name ∧ x.ty.IsType

mutual
/-- An op as read can be written, at any depth. -/
def SOp.Writable : SOp → Prop
  | ⟨results, name, _, attrs, _, succs, regions, loc⟩ =>
    (∀ x ∈ results, x.Writable) ∧ isWord name ∧ Attr.AllWritable attrs ∧
      (∀ s ∈ succs, s.Writable) ∧ SRegion.WritableList regions ∧ loc < Location.limit

/-- Regions as read can be written. -/
def SRegion.WritableList : List SRegion → Prop
  | [] => True
  | ⟨k, bs⟩ :: rs => (∀ w ∈ k, isWord w) ∧ SBlock.WritableList bs ∧ SRegion.WritableList rs

/-- Blocks as read can be written. -/
def SBlock.WritableList : List SBlock → Prop
  | [] => True
  | ⟨label, params, ops⟩ :: bs =>
    isName label ∧ (∀ x ∈ params, x.Writable) ∧ SOp.WritableList ops ∧ SBlock.WritableList bs

/-- Ops as read can be written. -/
def SOp.WritableList : List SOp → Prop
  | [] => True
  | o :: os => o.Writable ∧ SOp.WritableList os
end

mutual
/-- An item as read can be written: its parameters, its result types, its
attributes and its body. -/
def SItem.Writable : SItem → Prop
  | ⟨_, _, _, params, results, attrs, body⟩ =>
    (∀ x ∈ params, x.Writable) ∧ (∀ r ∈ results, r.1.IsType) ∧ (∀ a ∈ attrs, a.1.Writable) ∧
      SBody.Writable body

/-- The body of an item as read can be written: its blocks, or its dialect
set and its items. -/
def SBody.Writable : SBody → Prop
  | .blocks bs => SBlock.WritableList bs
  | .items ds is => (∀ x ∈ ds, isWord x) ∧ SItem.WritableList is

/-- Items as read can be written. -/
def SItem.WritableList : List SItem → Prop
  | [] => True
  | i :: is => i.Writable ∧ SItem.WritableList is
end

theorem SItem.writable_iff (i : SItem) : i.Writable ↔
    (∀ x ∈ i.params, x.Writable) ∧ (∀ r ∈ i.results, r.1.IsType) ∧
      (∀ a ∈ i.attrs, a.1.Writable) ∧ i.body.Writable := by
  obtain ⟨⟩ := i
  rfl

theorem SItem.writableList_iff : ∀ is : List SItem, SItem.WritableList is ↔ ∀ i ∈ is, i.Writable
  | [] => by simp [SItem.WritableList]
  | i :: is => by simp [SItem.WritableList, SItem.writableList_iff is]

/-- A module as read can be written: its dialect set, its items, and its
location table. -/
def SModule.Writable (s : SModule) : Prop :=
  (∀ x ∈ s.dialects, isWord x) ∧ (∀ i ∈ s.items, i.Writable) ∧ s.locs.InLimits

/-! # Reading tokens that can be written -/

theorem TokensWritable.tail {t : Token} {ts : List Token} (h : TokensWritable (t :: ts)) :
    TokensWritable ts :=
  fun u hu => h u (.tail _ hu)

theorem TokensWritable.value {n : Name} {p : TextPos} {ts : List Token}
    (h : TokensWritable (⟨.value n, p⟩ :: ts)) : isName n :=
  (h _ (.head _)).resolve_left nofun

theorem TokensWritable.label {n : Name} {p : TextPos} {ts : List Token}
    (h : TokensWritable (⟨.label n, p⟩ :: ts)) : isName n :=
  (h _ (.head _)).resolve_left nofun

theorem TokensWritable.word {w : String} {p : TextPos} {ts : List Token}
    (h : TokensWritable (⟨.word w, p⟩ :: ts)) : isWord w :=
  (h _ (.head _)).resolve_left nofun

theorem TokensWritable.float {l : FloatLit} {p : TextPos} {ts : List Token}
    (h : TokensWritable (⟨.float l, p⟩ :: ts)) : l.valid = true :=
  (h _ (.head _)).resolve_left nofun

theorem TokensWritable.locRef {r : Nat} {p : TextPos} {ts : List Token}
    (h : TokensWritable (⟨.locRef r, p⟩ :: ts)) : r < Location.limit :=
  (h _ (.head _)).resolve_left nofun

/-- `fail` reads nothing. -/
theorem fail_ne_ok {α : Type} {ts : List Token} {e : String} {a : α} : fail ts e ≠ .ok a := by
  unfold fail
  split <;> nofun

/-- On tokens `ts` that can be written, `read` gives what `P` holds of, and
leaves tokens that can be written. -/
def ReadsWritable {α : Type} {p : List Token → List Token → Prop}
    (read : (ts : List Token) → Except ParseError (α × {r : List Token // p r ts}))
    (P : α → Prop) (ts : List Token) : Prop :=
  TokensWritable ts → ∀ a r, read ts = .ok (a, r) → P a ∧ TokensWritable r.1

theorem expect_writable (tok : Tok) (e : String) (ts : List Token) :
    ReadsWritable (expect tok e) (fun _ => True) ts := by
  intro hw a r h
  unfold expect at h
  split at h
  · split at h
    · cases h
      exact ⟨trivial, hw.tail⟩
    · exact absurd h fail_ne_ok
  · exact absurd h fail_ne_ok

theorem keyword_writable (kw : String) (ts : List Token) :
    ReadsWritable (keyword kw) (fun _ => True) ts :=
  expect_writable _ _ ts

/-- `readMore item` gives what `P` holds of each time, when `item` does. -/
theorem readMore_writable {α : Type} {item : (ts : List Token) → Read α ts} {P : α → Prop}
    (hi : ∀ ts, ReadsWritable item P ts) :
    ∀ ts, ReadsWritable (readMore item) (fun xs => ∀ x ∈ xs, P x) ts := by
  intro ts
  induction ts using readMore.induct with
  | case1 pos rest ih =>
    intro hw xs r h
    rw [readMore.eq_1] at h
    bind_step h with ⟨⟨x, r₁, hr₁⟩, e₁, h⟩
    bind_step h with ⟨⟨xs', r₂, hr₂⟩, e₂, h⟩
    cases h
    obtain ⟨k₁, w₁⟩ := hi rest hw.tail x _ e₁
    obtain ⟨k₂, w₂⟩ := ih r₁ hr₁ w₁ xs' _ e₂
    exact ⟨fun y hy => (List.mem_cons.mp hy).elim (· ▸ k₁) (k₂ y), w₂⟩
  | case2 ts hne =>
    intro hw xs r h
    rw [readMore.eq_2 _ _ hne] at h
    cases h
    exact ⟨by simp, hw⟩

/-! # Attributes, definitions and successors as read -/

/-- Every attribute that the readers of attributes read can be written: its
words and the heads of its applied words are words. The three readers call
one another, and `readAttr.mutual_induct` ties them together. -/
theorem readAttr_writable :
    (∀ ts, ReadsWritable readAttr Attr.Writable ts) ∧
      (∀ ts, ReadsWritable readAttrArgs Attr.AllWritable ts) ∧
      (∀ ts, ReadsWritable readMoreAttrArgs Attr.AllWritable ts) := by
  refine readAttr.mutual_induct _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro w pos pos₁ rest ih hw a r h
    rw [readAttr.eq_1] at h
    bind_step h with ⟨⟨args, r₁, hr₁⟩, e₁, h⟩
    cases h
    obtain ⟨k, w₁⟩ := ih hw.tail.tail args _ e₁
    exact ⟨⟨hw.word, k⟩, w₁⟩
  · intro w pos rest hne hw a r h
    rw [readAttr.eq_2 _ _ _ hne] at h
    cases h
    exact ⟨hw.word, hw.tail⟩
  iterate 3
    · intro _ _ _ hw a r h
      simp only [readAttr] at h
      cases h
      exact ⟨trivial, hw.tail⟩
  · intro _ _ _ hw a r h
    simp only [readAttr] at h
    cases h
    exact ⟨hw.float, hw.tail⟩
  · intro ts h₁ h₂ h₃ h₄ h₅ h₆ hw a r h
    rw [readAttr.eq_7 _ h₁ h₂ h₃ h₄ h₅ h₆] at h
    exact absurd h fail_ne_ok
  · intro pos rest hw a r h
    rw [readAttrArgs.eq_1] at h
    cases h
    exact ⟨trivial, hw.tail⟩
  · intro ts hne ih₁ ih₂ hw a r h
    rw [readAttrArgs.eq_2 _ hne] at h
    bind_step h with ⟨⟨x, r₁, hr₁⟩, e₁, h⟩
    bind_step h with ⟨⟨xs, r₂, hr₂⟩, e₂, h⟩
    cases h
    obtain ⟨k₁, w₁⟩ := ih₁ hw x _ e₁
    obtain ⟨k₂, w₂⟩ := ih₂ r₁ hr₁ w₁ xs _ e₂
    exact ⟨⟨k₁, k₂⟩, w₂⟩
  · intro pos rest ih₁ ih₂ hw a r h
    rw [readMoreAttrArgs.eq_1] at h
    bind_step h with ⟨⟨x, r₁, hr₁⟩, e₁, h⟩
    bind_step h with ⟨⟨xs, r₂, hr₂⟩, e₂, h⟩
    cases h
    obtain ⟨k₁, w₁⟩ := ih₁ hw.tail x _ e₁
    obtain ⟨k₂, w₂⟩ := ih₂ r₁ hr₁ w₁ xs _ e₂
    exact ⟨⟨k₁, k₂⟩, w₂⟩
  · intro pos rest hw a r h
    rw [readMoreAttrArgs.eq_2] at h
    cases h
    exact ⟨trivial, hw.tail⟩
  · intro ts h₁ h₂ hw a r h
    rw [readMoreAttrArgs.eq_3 _ h₁ h₂] at h
    exact absurd h fail_ne_ok

/-- A type as read is a word, or a word applied to attributes, that can be
written: it is written as a type. -/
theorem readType_writable (ts : List Token) : ReadsWritable readType (·.1.IsType) ts := by
  intro hw a r h
  unfold readType at h
  split at h
  · bind_step h with ⟨⟨args, r₁, hr₁⟩, e₁, h⟩
    cases h
    obtain ⟨k, w₁⟩ := readAttr_writable.2.1 _ hw.tail.tail args _ e₁
    exact ⟨⟨hw.word, k⟩, w₁⟩
  · cases h
    exact ⟨hw.word, hw.tail⟩
  · exact absurd h fail_ne_ok

/-- Each attribute of an op as read can be written. -/
theorem readAttrs_writable :
    ∀ ts, ReadsWritable readAttrs (fun as => ∀ a ∈ as, a.1.Writable) ts := by
  intro ts
  induction ts using readAttrs.induct with
  | case1 t tail hs ih =>
    intro hw as r h
    rw [readAttrs, ite_eq_left hs] at h
    bind_step h with ⟨⟨x, r₁, hr₁⟩, e₁, h⟩
    bind_step h with ⟨⟨xs, r₂, hr₂⟩, e₂, h⟩
    cases h
    obtain ⟨k₁, w₁⟩ := readAttr_writable.1 _ hw x _ e₁
    obtain ⟨k₂, w₂⟩ := ih r₁ hr₁ w₁ xs _ e₂
    exact ⟨fun y hy => (List.mem_cons.mp hy).elim (· ▸ k₁) (k₂ y), w₂⟩
  | case2 t tail hs =>
    intro hw as r h
    rw [readAttrs, ite_eq_right hs] at h
    cases h
    exact ⟨by simp, hw⟩
  | case3 =>
    intro hw as r h
    rw [readAttrs] at h
    cases h
    exact ⟨by simp, hw⟩

/-- The type of the definition of `n`, after `n`, is written as a type. -/
theorem readDefType_writable (n : Name) (p : TextPos) (ts : List Token) :
    ReadsWritable (readDefType n p) (fun x => x.name = n ∧ x.ty.IsType) ts := by
  intro hw x r h
  unfold readDefType at h
  bind_step h with ⟨⟨_, a⟩, e₁, h⟩
  bind_step h with ⟨⟨⟨ty, tp⟩, b⟩, e₂, h⟩
  cases h
  obtain ⟨-, w₁⟩ := expect_writable _ _ _ hw _ _ e₁
  obtain ⟨k, w₂⟩ := readType_writable _ w₁ _ _ e₂
  exact ⟨⟨rfl, k⟩, w₂⟩

/-- A definition as read can be written: its value comes from a value
token. -/
theorem readDef_writable (ts : List Token) : ReadsWritable readDef SDef.Writable ts := by
  intro hw x r h
  unfold readDef at h
  split at h
  · bind_step h with ⟨⟨y, a⟩, e₁, h⟩
    cases h
    obtain ⟨⟨hn, k⟩, w₁⟩ := readDefType_writable _ _ _ hw.tail _ _ e₁
    exact ⟨⟨hn ▸ hw.value, k⟩, w₁⟩
  · exact absurd h fail_ne_ok

theorem readDefs_writable (ts : List Token) :
    ReadsWritable readDefs (fun xs => ∀ x ∈ xs, x.Writable) ts := by
  intro hw xs r h
  unfold readDefs at h
  bind_step h with ⟨⟨x, a⟩, e₁, h⟩
  bind_step h with ⟨⟨xs', b⟩, e₂, h⟩
  cases h
  obtain ⟨k₁, w₁⟩ := readDef_writable _ hw _ _ e₁
  obtain ⟨k₂, w₂⟩ := readMore_writable readDef_writable _ w₁ _ _ e₂
  exact ⟨fun y hy => (List.mem_cons.mp hy).elim (· ▸ k₁) (k₂ y), w₂⟩

/-- The values passed to a successor come from value tokens. -/
theorem readSuccArgs_writable :
    ∀ ts, ReadsWritable readSuccArgs (fun vs => ∀ v ∈ vs, isName v) ts := by
  intro ts
  induction ts using readSuccArgs.induct with
  | case1 v pos pos₁ rest ih =>
    intro hw vs r h
    rw [readSuccArgs.eq_1] at h
    bind_step h with ⟨⟨vs', r₁, hr₁⟩, e₁, h⟩
    cases h
    obtain ⟨k, w₁⟩ := ih hw.tail.tail vs' _ e₁
    exact ⟨fun y hy => (List.mem_cons.mp hy).elim (· ▸ hw.value) (k y), w₁⟩
  | case2 v pos rest hne =>
    intro hw vs r h
    rw [readSuccArgs.eq_2 _ _ _ hne] at h
    bind_step h with ⟨⟨_, a⟩, e₁, h⟩
    cases h
    obtain ⟨-, w₁⟩ := expect_writable _ _ _ hw.tail _ _ e₁
    exact ⟨by simpa using hw.value, w₁⟩
  | case3 ts h₁ h₂ =>
    intro hw vs r h
    rw [readSuccArgs.eq_3 _ h₁ h₂] at h
    exact absurd h fail_ne_ok

/-- A successor as read can be written: its label comes from a label
token. -/
theorem readSucc_writable (ts : List Token) : ReadsWritable readSucc Succ.Writable ts := by
  intro hw s r h
  unfold readSucc at h
  split at h
  · bind_step h with ⟨⟨args, r₁, hr₁⟩, e₁, h⟩
    cases h
    obtain ⟨k, w₁⟩ := readSuccArgs_writable _ hw.tail.tail args _ e₁
    exact ⟨⟨hw.label, k⟩, w₁⟩
  · cases h
    exact ⟨⟨hw.label, by simp⟩, hw.tail⟩
  · exact absurd h fail_ne_ok

theorem readMoreOperands_writable :
    ∀ ts, ReadsWritable readMoreOperands (fun x => ∀ s ∈ x.2, s.Writable) ts := by
  intro ts
  induction ts using readMoreOperands.induct with
  | case1 pos v p rest ih =>
    intro hw x r h
    rw [readMoreOperands.eq_1] at h
    bind_step h with ⟨⟨⟨vs, ss⟩, r₁, hr₁⟩, e₁, h⟩
    cases h
    exact ih hw.tail.tail _ _ e₁
  | case2 ts hne =>
    intro hw x r h
    rw [readMoreOperands.eq_2 _ hne] at h
    bind_step h with ⟨⟨ss, a⟩, e₁, h⟩
    cases h
    exact readMore_writable readSucc_writable _ hw _ _ e₁

/-- An op's successors as read can be written. -/
theorem readOperands_writable (ts : List Token) :
    ReadsWritable readOperands (fun x => ∀ s ∈ x.2, s.Writable) ts := by
  intro hw x r h
  unfold readOperands at h
  split at h
  · bind_step h with ⟨⟨⟨vs, ss⟩, a⟩, e₁, h⟩
    cases h
    obtain ⟨k, w₁⟩ := readMoreOperands_writable _ hw.tail _ _ e₁
    exact ⟨k, w₁⟩
  · bind_step h with ⟨⟨s, a⟩, e₁, h⟩
    bind_step h with ⟨⟨ss, b⟩, e₂, h⟩
    cases h
    obtain ⟨k₁, w₁⟩ := readSucc_writable _ hw _ _ e₁
    obtain ⟨k₂, w₂⟩ := readMore_writable readSucc_writable _ w₁ _ _ e₂
    exact ⟨fun y hy => (List.mem_cons.mp hy).elim (· ▸ k₁) (k₂ y), w₂⟩
  · cases h
    exact ⟨by simp, hw⟩

/-- An op's location reference as read is below `2^32`. -/
theorem readOpLoc_writable (ts : List Token) :
    ReadsWritable readOpLoc (· < Location.limit) ts := by
  intro hw x r h
  unfold readOpLoc at h
  split at h
  · cases h
    exact ⟨hw.locRef, hw.tail⟩
  · exact absurd h fail_ne_ok

/-- A region's kind as read is a word, and leaves tokens that can be
written. -/
theorem readKind_writable (ts : List Token) :
    ReadsWritable readKind (fun k => ∀ w ∈ k, isWord w) ts := by
  intro hw k r h
  unfold readKind at h
  split at h
  · cases h
    exact ⟨fun w hw' => by cases hw'; exact hw.word, hw.tail⟩
  · cases h
    exact ⟨by simp, hw⟩

end Fir.Text
