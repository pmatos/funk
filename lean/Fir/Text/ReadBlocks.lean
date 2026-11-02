import Fir.Text.ReadOps

/-!
# Reading blocks and regions

Blocks read back before a `}`, which starts no block, and regions before a
location reference, which ends the op that owns them. A block's arguments
are read as definitions when there are any, and its `:` alone when there
are none.

The lemmas for blocks and regions, like those for ops, take as hypotheses
what the readers that they call do. The last four lemmas tie them all
together, one for each reader, by structural recursion on the blocks, ops
and regions of a module, at any depth.
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

variable {d : Dialect} [DialectText d]

/-- Blocks start with a label. -/
theorem head_blocks (bs : List (Block d)) (rest : List Tok) (P : Tok → Prop)
    (hl : ∀ l, P (.label l)) (hr : ∀ t ∈ rest.head?, P t) :
    ∀ t ∈ (Block.tokensList bs ++ rest).head?, P t := by
  cases bs with
  | nil => simpa [Block.tokensList] using hr
  | cons b bs => obtain ⟨_, _, _⟩ := b; simp [Block.tokensList, hl]

/-- `readBlocks` reads no blocks before a `}`. -/
theorem readBlocks_nil_reads :
    Reads readBlocks SBlock.eraseList (Block.treeList ([] : List (Block d)))
      (Block.tokensList ([] : List (Block d))) (· = .rbrace) := by
  intro ts rest h hs
  simp only [Block.tokensList, List.nil_append] at h
  rw [readBlocks.eq_3 _ fun l p r he => by
    subst he
    exact absurd (hs (.label l) (by rw [← h]; rfl)) (by simp)]
  exact ⟨[], _, rfl, rfl, h⟩

/-- `readBlocks` reads a block and the blocks after it, when `readOps` reads
the block's ops and `readBlocks` the blocks after it. -/
theorem readBlocks_cons_reads {label : Name} {params : List (Name × d.Ty)}
    {body : List (Operation d)} {bs : List (Block d)}
    (hp : ∀ x ∈ params, (tyAttr x.2).IsType)
    (hops : Reads readOps SOp.eraseList (Operation.treeList body) (Operation.tokensList body)
      EndsOps)
    (hbs : Reads readBlocks SBlock.eraseList (Block.treeList bs) (Block.tokensList bs)
      (· = .rbrace)) :
    Reads readBlocks SBlock.eraseList (Block.treeList (⟨label, params, body⟩ :: bs))
      (Block.tokensList (⟨label, params, body⟩ :: bs)) (· = .rbrace) := by
  intro ts rest h hs
  have hstop := head_blocks bs rest EndsOps (fun l => .inr ⟨l, rfl⟩) fun t ht => .inl (hs t ht)
  simp only [Block.tokensList, List.cons_append, List.append_assoc] at h
  take_tok h
  cases params with
  | nil =>
    simp only [List.isEmpty_nil, ↓reduceIte, List.nil_append] at h
    rw [readBlocks.eq_2 _ _ _ (not_cons_of_head h (by simp))]
    take_tok h
    obtain ⟨sos, ⟨r, hr⟩, h₁, h₂, h₃⟩ := hops _ (Block.tokensList bs ++ rest) h hstop
    obtain ⟨sbs, ⟨r', hr'⟩, h₄, h₅, h₆⟩ := hbs r rest h₃ hs
    simp only [After.here, pure_bind, expect_cons, ok_bind, h₁, h₄]
    exact ⟨_, _, rfl, by simp [SBlock.eraseList, Block.treeList, h₂, h₅], h₆⟩
  | cons x xs =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.cons_append,
      List.append_assoc] at h
    take_tok h
    obtain ⟨sds, ⟨r₀, hr₀⟩, h₀, h₀', h₀''⟩ := readDefs_reads (List.cons_ne_nil x xs) hp _ _ h
      (by simp)
    take_tok h₀''
    take_tok h₀''
    obtain ⟨sos, ⟨r, hr⟩, h₁, h₂, h₃⟩ := hops _ (Block.tokensList bs ++ rest) h₀'' hstop
    obtain ⟨sbs, ⟨r', hr'⟩, h₄, h₅, h₆⟩ := hbs r rest h₃ hs
    rw [readBlocks.eq_1]
    simp only [h₀, After.then, After.next, pure_bind, expect_cons, ok_bind, h₁, h₄]
    exact ⟨_, _, rfl, by simp [SBlock.eraseList, Block.treeList, h₀', h₂, h₅], h₆⟩

/-- `readRegions` reads no regions before a location reference. -/
theorem readRegions_nil_reads :
    Reads readRegions SRegion.eraseList (Region.treeList ([] : List (Region d)))
      (Region.tokensList ([] : List (Region d))) (fun t => ∃ r, t = .locRef r) := by
  intro ts rest h hs
  simp only [Region.tokensList, List.nil_append] at h
  rw [readRegions.eq_2 _ fun p r he => by
    subst he
    obtain ⟨_, h'⟩ := hs .lbrace (by rw [← h]; rfl)
    exact absurd h' (by simp)]
  exact ⟨[], _, rfl, rfl, h⟩

/-- `readRegions` reads a region and the regions after it, when
`readBlocks` reads the region's blocks and `readRegions` the regions after
it. -/
theorem readRegions_cons_reads {blocks : List (Block d)} {rs : List (Region d)}
    (hb : Reads readBlocks SBlock.eraseList (Block.treeList blocks) (Block.tokensList blocks)
      (· = .rbrace))
    (hrs : Reads readRegions SRegion.eraseList (Region.treeList rs) (Region.tokensList rs)
      (fun t => ∃ r, t = .locRef r)) :
    Reads readRegions SRegion.eraseList (Region.treeList (⟨blocks⟩ :: rs))
      (Region.tokensList (⟨blocks⟩ :: rs)) (fun t => ∃ r, t = .locRef r) := by
  intro ts rest h hs
  simp only [Region.tokensList, List.cons_append, List.append_assoc] at h
  take_tok h
  obtain ⟨sbs, ⟨r, hr⟩, h₁, h₂, h₃⟩ := hb _ _ h (by simp)
  take_tok h₃
  obtain ⟨srs, ⟨r', hr'⟩, h₄, h₅, h₆⟩ := hrs _ rest h₃ hs
  rw [readRegions.eq_1]
  simp only [h₁, ok_bind, expect_cons, h₄]
  exact ⟨_, _, rfl, by simp [SRegion.eraseList, Region.treeList, h₂, h₅], h₆⟩

mutual
/-- `readBlocks` reads blocks' tokens as their trees, before a `}`. -/
theorem Block.readsList : ∀ bs : List (Block d),
    (∀ b ∈ Block.allBlocks bs, ∀ x ∈ b.defs, (tyAttr x.2).IsType) →
    Reads readBlocks SBlock.eraseList (Block.treeList bs) (Block.tokensList bs) (· = .rbrace)
  | [], _ => readBlocks_nil_reads
  | ⟨label, params, body⟩ :: bs, hty =>
    have hb : ∀ x ∈ Block.defs ⟨label, params, body⟩, (tyAttr x.2).IsType :=
      hty _ (by simp [Block.allBlocks])
    readBlocks_cons_reads (fun x hx => hb x (List.mem_append_left _ hx))
      (Operation.readsList body
        (fun o ho x hx => hb x (List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, ho, hx⟩)))
        (fun b hb' => hty b (by simp [Block.allBlocks, hb'])))
      (Block.readsList bs fun b hb' => hty b (by simp [Block.allBlocks, hb']))

/-- `readOps` reads ops' tokens as their trees, before a label or a `}`. -/
theorem Operation.readsList : ∀ os : List (Operation d),
    (∀ o ∈ os, ∀ x ∈ o.results, (tyAttr x.2).IsType) →
    (∀ b ∈ Operation.regionBlocks os, ∀ x ∈ b.defs, (tyAttr x.2).IsType) →
    Reads readOps SOp.eraseList (Operation.treeList os) (Operation.tokensList os) EndsOps
  | [], _, _ => readOps_nil_reads
  | o :: os, hres, hreg =>
    have hsub : ∀ b ∈ Region.allBlocks o.regions, b ∈ Operation.regionBlocks (o :: os) := by
      obtain ⟨_, _, _, _, _, _⟩ := o
      intro b hb
      simp [Operation.regionBlocks, hb]
    have hrest : ∀ b ∈ Operation.regionBlocks os, b ∈ Operation.regionBlocks (o :: os) := by
      obtain ⟨_, _, _, _, _, _⟩ := o
      intro b hb
      simp [Operation.regionBlocks, hb]
    readOps_cons_reads (hres o (.head _))
      (Operation.readsBody o fun b hb => hreg b (hsub b hb))
      (Operation.readsList os (fun o' ho' => hres o' (.tail _ ho')) fun b hb => hreg b (hrest b hb))

/-- `readOpBody` reads the tokens of an op after its name as the rest of the
op. -/
theorem Operation.readsBody : ∀ o : Operation d,
    (∀ b ∈ Region.allBlocks o.regions, ∀ x ∈ b.defs, (tyAttr x.2).IsType) →
    ∀ (res : List SDef) (w : String) (p : TextPos),
    Reads (readOpBody res w p) SOp.erase (o.treeWith (res.map SDef.erase) w) o.tokensAfterName
      (fun _ => True)
  | ⟨results, op, operands, succs, regions, loc⟩, hreg =>
    readOpBody_reads ⟨results, op, operands, succs, regions, loc⟩ (Region.readsList regions hreg)

/-- `readRegions` reads regions' tokens as their trees, before a location
reference. -/
theorem Region.readsList : ∀ rs : List (Region d),
    (∀ b ∈ Region.allBlocks rs, ∀ x ∈ b.defs, (tyAttr x.2).IsType) →
    Reads readRegions SRegion.eraseList (Region.treeList rs) (Region.tokensList rs)
      (fun t => ∃ r, t = .locRef r)
  | [], _ => readRegions_nil_reads
  | ⟨blocks⟩ :: rs, hty =>
    readRegions_cons_reads (Block.readsList blocks fun b hb => hty b (by simp [Region.allBlocks, hb]))
      (Region.readsList rs fun b hb => hty b (by simp [Region.allBlocks, hb]))
end

end Fir
