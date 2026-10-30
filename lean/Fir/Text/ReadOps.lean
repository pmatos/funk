import Fir.Text.ReadDefs

/-!
# Reading ops

An op's tokens read back as the op's tree, whatever follows them: the op
ends with its location reference, which `readOpLoc` reads alone. Ops read
back before a label or a `}`, which start no op. Each type that a
definition states must be written as a type.

The readers of ops, blocks and regions call one another. So each lemma
here takes as a hypothesis what the readers that it calls do, and the next
section ties the lemmas together, by structural recursion on the ops,
blocks and regions of a module.
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

/-- An op's results and its `=`, when it has results. -/
theorem lhs_tokens (results : List (Name × d.Ty)) :
    (if results.isEmpty = true then [] else defsTokens results ++ [Tok.eq]) =
      if results = [] then [] else defsTokens results ++ [Tok.eq] := by
  cases results <;> rfl

/-- An op's name and attributes, then its operands and successors after
them, separated by commas. -/
theorem rhs_tokens (head : List Tok) (uses : List (List Tok)) :
    (if uses.isEmpty = true then head else head ++ [Tok.comma].intercalate uses) =
      head ++ [Tok.comma].intercalate uses := by
  cases uses <;> simp

/-- What follows an op's attributes: an operand, a successor, a region or
its location reference. None starts an attribute, and none is `(`. -/
theorem head_uses (operands : List Name) (succs : List Succ) (regions : List (Region d))
    (loc : LocRef) (rest : List Tok) :
    ∀ t ∈ ([Tok.comma].intercalate (operands.map ([.value ·]) ++ succs.map Succ.tokens) ++
      (Region.tokensList regions ++ .locRef loc :: rest)).head?,
      t.startsAttr = false ∧ t ≠ .lparen := by
  cases operands with
  | cons v vs => simp [intercalate_cons, Tok.startsAttr]
  | nil =>
    cases succs with
    | cons s ss => simp [intercalate_cons, Succ.tokens, Tok.startsAttr]
    | nil =>
      cases regions with
      | nil => simp [Region.tokensList, Tok.startsAttr]
      | cons r rs => obtain ⟨_⟩ := r; simp [Region.tokensList, Tok.startsAttr]

/-- What follows an op's operands and successors: a region or its location
reference. -/
theorem head_regions (regions : List (Region d)) (loc : LocRef) (rest : List Tok) :
    ∀ t ∈ (Region.tokensList regions ++ .locRef loc :: rest).head?, EndsUses t := by
  cases regions with
  | nil => simp [Region.tokensList, EndsUses]
  | cons r rs => obtain ⟨_⟩ := r; simp [Region.tokensList, EndsUses]

/-- What follows the ops of a block: a label or a `}`. -/
def EndsOps (t : Tok) : Prop := t = .rbrace ∨ ∃ l, t = .label l

/-- The tokens of an op after its name: its attributes, its operands and
successors, its regions and its location reference. -/
def Operation.tokensAfterName (o : Operation d) : List Tok :=
  (opAttrs o.op).flatMap Attr.tokens ++
    ([Tok.comma].intercalate (o.operands.map ([.value ·]) ++ o.succs.map Succ.tokens) ++
      (Region.tokensList o.regions ++ [.locRef o.loc]))

/-- The tree of an op whose results are written as `rs`, without positions,
and whose name is written `w`. -/
def Operation.treeWith (o : Operation d) (rs : List SDef) (w : String) : SOp :=
  ⟨rs, w, .zero, opAttrs o.op, o.operands.map (·, .zero), o.succs, Region.treeList o.regions,
    o.loc⟩

/-- An op's tokens: its results and `=`, when it has results, then its name
and the rest. -/
theorem Operation.tokens_eq (o : Operation d) :
    o.tokens = (if o.results = [] then [] else defsTokens o.results ++ [Tok.eq]) ++
      .word (opName o.op) :: o.tokensAfterName := by
  obtain ⟨results, op, operands, succs, regions, loc⟩ := o
  simp only [Operation.tokens]
  rw [lhs_tokens, rhs_tokens]
  simp only [Operation.tokensAfterName, List.append_assoc, List.cons_append]

/-- `readOpBody` reads the tokens of an op after its name as the rest of the
op, when `readRegions` reads its regions. -/
theorem readOpBody_reads (o : Operation d)
    (hrs : Reads readRegions SRegion.eraseList (Region.treeList o.regions)
      (Region.tokensList o.regions) (fun t => ∃ r, t = .locRef r))
    (res : List SDef) (w : String) (p : TextPos) :
    Reads (readOpBody res w p) SOp.erase (o.treeWith (res.map SDef.erase) w) o.tokensAfterName
      (fun _ => True) := by
  intro ts rest h _
  obtain ⟨results, op, operands, succs, regions, loc⟩ := o
  simp only [Operation.tokensAfterName, List.append_assoc, List.singleton_append] at h
  obtain ⟨attrs, ⟨r₁, hr₁⟩, h₁, h₂, h₃⟩ := readAttrs_reads (opAttrs op) ts _ h
    (head_uses operands succs regions loc rest)
  obtain ⟨⟨vs, ss⟩, ⟨r₂, hr₂⟩, h₄, h₅, h₆⟩ := readOperands_reads operands succs r₁ _ h₃
    (head_regions regions loc rest)
  obtain ⟨srs, ⟨r₃, hr₃⟩, h₇, h₈, h₉⟩ := hrs r₂ (.locRef loc :: rest) h₆ (by simp)
  obtain ⟨l, ⟨r₄, hr₄⟩, h₁₀, h₁₁, h₁₂⟩ := readOpLoc_reads loc r₃ rest h₉ fun _ _ => trivial
  rw [readOpBody.eq_1]
  simp only [h₁, ok_bind, h₄, h₇, h₁₀]
  simp only [Prod.mk.injEq] at h₅
  exact ⟨_, _, rfl, by simp [SOp.erase, Operation.treeWith, h₂, h₅.1, h₅.2, h₈, ← h₁₁], h₁₂⟩

/-- `readOpWithResults` reads the tokens of an op after its first result's
value, when `readOpBody` reads the tokens after its name. -/
theorem readOpWithResults_reads {o : Operation d} {x : Name × d.Ty} {xs : List (Name × d.Ty)}
    {w : String} (hx : ∀ y ∈ x :: xs, (tyAttr y.2).IsType)
    (hbody : ∀ res p, Reads (readOpBody res w p) SOp.erase (o.treeWith (res.map SDef.erase) w)
      o.tokensAfterName (fun _ => True))
    (p : TextPos) :
    Reads (readOpWithResults x.1 p) SOp.erase (o.treeWith ((x :: xs).map defTree) w)
      (.colon :: (tyAttr x.2).tokens ++ xs.flatMap (.comma :: defTokens ·) ++
        .eq :: .word w :: o.tokensAfterName) (fun _ => True) := by
  intro ts rest h _
  simp only [List.cons_append, List.append_assoc] at h
  obtain ⟨sd, ⟨r₁, hr₁⟩, h₁, h₂, h₃⟩ := readDefType_reads p (hx x (.head _)) _ _ h
    (head?_append _ (by cases xs <;> simp) (by simp))
  obtain ⟨sds, ⟨r₂, hr₂⟩, h₄, h₅, h₆⟩ := Reads.more (stop := (· ≠ .lparen)) (by decide)
    (stop' := fun t => t = .eq) (fun t ht => by subst ht; decide)
    (fun y hy => readDef_reads (hx y (.tail _ hy))) r₁ _ h₃ (by simp)
  take_tok h₆
  take_pos h₆ wp
  obtain ⟨so, ⟨r, hr⟩, h₇, h₈, h₉⟩ := hbody (sd :: sds) wp _ rest h₆ fun _ _ => trivial
  rw [readOpWithResults.eq_1]
  simp only [h₁, ok_bind, h₄, h₇]
  exact ⟨_, _, rfl, by simp [h₈, h₂, h₅], h₉⟩

/-- `readOps` reads no ops before a label or a `}`. -/
theorem readOps_nil_reads :
    Reads readOps SOp.eraseList (Operation.treeList ([] : List (Operation d)))
      (Operation.tokensList ([] : List (Operation d))) EndsOps := by
  intro ts rest h hs
  simp only [Operation.tokensList, List.nil_append] at h
  rw [readOps.eq_3 _
    (fun v p r he => by subst he; simpa [EndsOps] using hs (.value v) (by rw [← h]; rfl))
    (fun w p r he => by subst he; simpa [EndsOps] using hs (.word w) (by rw [← h]; rfl))]
  exact ⟨[], _, rfl, rfl, h⟩

/-- `readOps` reads an op and the ops after it, when `readOpBody` reads the
op's tokens after its name and `readOps` reads the ops after it. -/
theorem readOps_cons_reads {o : Operation d} {os : List (Operation d)}
    (hr : ∀ x ∈ o.results, (tyAttr x.2).IsType)
    (hbody : ∀ res w p, Reads (readOpBody res w p) SOp.erase (o.treeWith (res.map SDef.erase) w)
      o.tokensAfterName (fun _ => True))
    (hos : Reads readOps SOp.eraseList (Operation.treeList os) (Operation.tokensList os) EndsOps) :
    Reads readOps SOp.eraseList (Operation.treeList (o :: os)) (Operation.tokensList (o :: os))
      EndsOps := by
  intro ts rest h hs
  have ht : o.tree = o.treeWith (o.results.map defTree) (opName o.op) := by
    obtain ⟨_, _, _, _, _, _⟩ := o
    rfl
  simp only [Operation.tokensList, Operation.tokens_eq, List.append_assoc] at h
  cases hres : o.results with
  | nil =>
    simp only [hres, ↓reduceIte, List.nil_append, List.cons_append] at h ht
    take_pos h p
    obtain ⟨so, ⟨r, hr'⟩, h₁, h₂, h₃⟩ := hbody [] (opName o.op) p _ _ h fun _ _ => trivial
    obtain ⟨sos, ⟨r', hr''⟩, h₄, h₅, h₆⟩ := hos r rest h₃ hs
    rw [readOps.eq_2]
    simp only [h₁, ok_bind, h₄]
    exact ⟨_, _, rfl, by simp [SOp.eraseList, Operation.treeList, ht, h₂, h₅], h₆⟩
  | cons x xs =>
    rw [hres] at hr ht
    simp only [hres, reduceCtorEq, ↓reduceIte, defsTokens, List.map_cons, intercalate_cons,
      flatMap_comma_map, List.cons_append, List.nil_append, List.append_assoc] at h
    rw [defTokens] at h
    take_pos h p
    obtain ⟨so, ⟨r, hr'⟩, h₁, h₂, h₃⟩ := readOpWithResults_reads hr (hbody · (opName o.op)) p _
      (Operation.tokensList os ++ rest)
      (by simpa only [List.append_eq, List.cons_append, List.append_assoc] using h)
      fun _ _ => trivial
    obtain ⟨sos, ⟨r', hr''⟩, h₄, h₅, h₆⟩ := hos r rest h₃ hs
    rw [readOps.eq_1]
    simp only [h₁, ok_bind, h₄]
    exact ⟨_, _, rfl, by simp [SOp.eraseList, Operation.treeList, ht, h₂, h₅], h₆⟩

end Fir
