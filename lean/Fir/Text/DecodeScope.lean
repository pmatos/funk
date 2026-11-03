import Fir.Text.Decode
import Fir.Text.LexTokens
import Fir.Text.Tree

/-!
# The scope that decoding builds

The last step of the parser decodes the tree that the grammar reads, and
the last step of #11's proof shows that it gives the module back: on any
tree that erases to the tree of a well-formed module, `decodeModule` gives
the module. Decoding a function takes two passes, and this section is about
the first. It reads every definition of the function, at any depth, and
builds the function's scope: each value it defines, with its type.

The first pass reads the parameters, then each block's arguments, then for
each op its results and then the blocks of its regions. `Block.scopeDefs`
lists the definitions of blocks in that order. `Func.defs` lists all of a
block's op results before the blocks of their regions, so the two lists
differ, but only in order: each is a permutation of the other
(`Block.scopeDefs_perm`, `Func.scopeDefs_perm`).

`Scope.Holds sc L` says that the scope `sc` gives each value of `L` its
type, and gives no other value a type. Each definition the pass reads adds
one value to the scope. Since a well-formed function names each value once,
the pass never finds a value twice, and the scope it builds holds exactly
the function's definitions. The type of each value is then the one that
`Func.typeOf` gives it (`Func.WellFormed.scope`), whatever the order.

Like the readers' lemmas of the grammar step, the lemmas for blocks, ops
and regions take what the passes they call do as hypotheses, and three
short mutual theorems tie them together by structural recursion.
-/

namespace Fir

open Text

variable {d : Dialect}

/-! # The order of the first pass -/

mutual
/-- The definitions of blocks, at any depth, in the order that the first
pass of decoding reads them: each block's arguments, then its ops'. -/
def Block.scopeDefs : List (Block d) → List (Name × d.Ty)
  | [] => []
  | ⟨_, params, body⟩ :: bs => params ++ Operation.scopeDefs body ++ Block.scopeDefs bs

/-- The definitions of ops, at any depth, in the order that the first pass
reads them: each op's results, then the blocks of its regions. -/
def Operation.scopeDefs : List (Operation d) → List (Name × d.Ty)
  | [] => []
  | ⟨results, _, _, _, regions, _⟩ :: os =>
    results ++ Region.scopeDefs regions ++ Operation.scopeDefs os

/-- The definitions of the blocks of regions, at any depth, in the order
that the first pass reads them. -/
def Region.scopeDefs : List (Region d) → List (Name × d.Ty)
  | [] => []
  | ⟨bs⟩ :: rs => Block.scopeDefs bs ++ Region.scopeDefs rs
end

mutual
/-- The first pass reads the definitions of blocks in another order than
`Block.defs` lists them, but reads the same ones. -/
theorem Block.scopeDefs_perm : ∀ bs : List (Block d),
    (Block.scopeDefs bs).Perm ((Block.allBlocks bs).flatMap Block.defs)
  | [] => by simp [Block.scopeDefs, Block.allBlocks]
  | ⟨label, params, body⟩ :: bs => by
    have h₁ := Operation.scopeDefs_perm body
    have h₂ := Block.scopeDefs_perm bs
    simp only [Block.scopeDefs, Block.allBlocks, List.cons_append, List.flatMap_cons,
      List.flatMap_append, Block.defs, List.append_assoc] at h₁ ⊢
    simpa only [List.append_assoc] using (h₁.append h₂).append_left params

/-- The definitions of ops, at any depth: their results, and the blocks of
their regions. -/
theorem Operation.scopeDefs_perm : ∀ os : List (Operation d),
    (Operation.scopeDefs os).Perm
      (os.flatMap (·.results) ++ (Operation.regionBlocks os).flatMap Block.defs)
  | [] => by simp [Operation.scopeDefs, Operation.regionBlocks]
  | ⟨results, op, operands, succs, regions, loc⟩ :: os => by
    have h₁ := Region.scopeDefs_perm regions
    have h₂ := Operation.scopeDefs_perm os
    simp only [Operation.scopeDefs, Operation.regionBlocks, List.flatMap_cons,
      List.flatMap_append, List.append_assoc]
    exact ((h₁.append h₂).trans (List.perm_append_comm_assoc _ _ _)).append_left results

/-- The definitions of the blocks of regions, at any depth. -/
theorem Region.scopeDefs_perm : ∀ rs : List (Region d),
    (Region.scopeDefs rs).Perm ((Region.allBlocks rs).flatMap Block.defs)
  | [] => by simp [Region.scopeDefs, Region.allBlocks]
  | ⟨bs⟩ :: rs => by
    simp only [Region.scopeDefs, Region.allBlocks, List.flatMap_append]
    exact (Block.scopeDefs_perm bs).append (Region.scopeDefs_perm rs)
end

/-- A function's definitions, in the order that the first pass reads them,
are its definitions. -/
theorem Func.scopeDefs_perm (f : Func d) : (f.params ++ Block.scopeDefs f.blocks).Perm f.defs :=
  (Block.scopeDefs_perm f.blocks).append_left f.params

/-- When names are unique, a value has the type of its one definition. -/
theorem find?_fst_eq_some {L : List (Name × d.Ty)} (h : (L.map (·.1)).Nodup) {x : Name}
    {t : d.Ty} : (L.find? (·.1 == x)).map (·.2) = some t ↔ (x, t) ∈ L := by
  induction L with
  | nil => simp
  | cons p L ih =>
    obtain ⟨y, u⟩ := p
    simp only [List.map_cons, List.nodup_cons] at h
    by_cases hy : y = x
    · subst hy
      have hn : (y, t) ∉ L := fun hm => h.1 (List.mem_map.mpr ⟨_, hm, rfl⟩)
      simp [hn, eq_comm]
    · have hb : (y == x) = false := by simpa using hy
      have hx : x ≠ y := fun he => hy he.symm
      simp [hb, ih h.2, hx]

end Fir

namespace Fir.Text

variable {d : Dialect}

/-! # Scopes -/

/-- The scope `sc` gives each value of `L` its type, and no other value a
type. -/
def Scope.Holds (sc : Scope d) (L : List (Name × d.Ty)) : Prop :=
  ∀ x t, sc[x]? = some t ↔ (x, t) ∈ L

/-- The empty scope holds no values. -/
theorem Scope.holds_empty : (∅ : Scope d).Holds [] := by
  intro x t
  simp

/-- A scope holds no value that its list does not name. -/
theorem Scope.Holds.contains_eq_false {sc : Scope d} {L : List (Name × d.Ty)} (h : sc.Holds L)
    {n : Name} (hn : n ∉ L.map (·.1)) : sc.contains n = false := by
  rw [Std.HashMap.contains_eq_isSome_getElem?]
  cases hx : sc[n]? with
  | none => rfl
  | some t => exact absurd (List.mem_map.mpr ⟨_, (h n t).mp hx, rfl⟩) hn

/-- Adding a value that the list does not name adds it to the list. -/
theorem Scope.Holds.insert {sc : Scope d} {L : List (Name × d.Ty)} (h : sc.Holds L) {n : Name}
    {t : d.Ty} (hn : n ∉ L.map (·.1)) : Scope.Holds (sc.insert n t) (L ++ [(n, t)]) := by
  intro x t'
  rw [Std.HashMap.getElem?_insert]
  by_cases hx : n = x
  · subst hx
    have hm : (n, t') ∉ L := fun hm => hn (List.mem_map.mpr ⟨_, hm, rfl⟩)
    simp [hm, eq_comm]
  · have hx' : x ≠ n := fun he => hx he.symm
    simp [hx, hx', h x t']

/-- Names are unique in the first part of a list whose names are unique. -/
theorem nodup_fst_left {L M : List (Name × d.Ty)} (h : ((L ++ M).map (·.1)).Nodup) :
    (L.map (·.1)).Nodup := by
  rw [List.map_append] at h
  exact List.Nodup.sublist (List.sublist_append_left _ _) h

variable [DialectText d]

/-- A definition that erases to a definition's tree decodes as that
definition, when its type decodes. -/
theorem decodeDef_eq {x : SDef} {y : Name × d.Ty} (hx : x.erase = defTree y)
    (ht : decodeTy (tyAttr y.2) = some y.2) : decodeDef x = .ok y := by
  obtain ⟨hn, hty⟩ := SDef.erase_eq_defTree.mp hx
  obtain ⟨n, p, a, q⟩ := x
  obtain ⟨n', t⟩ := y
  dsimp only at hn hty ht
  subst hn hty
  simp only [decodeDef, decodeType, ht] <;> rfl

/-- Definitions that erase to definitions' trees decode as those
definitions, when their types decode. -/
theorem mapM_decodeDef :
    ∀ {xs : List SDef} {ys : List (Name × d.Ty)}, xs.map SDef.erase = ys.map defTree →
      (∀ y ∈ ys, decodeTy (tyAttr y.2) = some y.2) → xs.mapM decodeDef = .ok ys
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: xs, y :: ys, h, hty => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.mapM_cons, decodeDef_eq h.1 (hty y (.head _)), ok_bind,
      mapM_decodeDef h.2 fun y' hy' => hty y' (.tail _ hy')] <;> rfl

/-! # The first pass -/

/-- `define` adds what erases to `tree` to any scope that holds `L`, and
the scope then holds `L ++ ys`, as long as no value is named twice. -/
def Defines {α β : Type} (define : Scope d → α → Except ParseError (Scope d)) (erase : α → β)
    (tree : β) (ys : List (Name × d.Ty)) : Prop :=
  ∀ a, erase a = tree → ∀ sc L, sc.Holds L → ((L ++ ys).map (·.1)).Nodup →
    ∃ sc', define sc a = .ok sc' ∧ sc'.Holds (L ++ ys)

/-- `define` adds definitions whose types decode. -/
theorem define_defines :
    ∀ {ys : List (Name × d.Ty)}, (∀ y ∈ ys, decodeTy (tyAttr y.2) = some y.2) →
      Defines define (List.map SDef.erase) (ys.map defTree) ys
  | [], _, xs, h, sc, L, hsc, _ => by
    simp only [List.map_nil, List.map_eq_nil_iff] at h
    subst h
    exact ⟨sc, by simp only [define] <;> rfl, by simpa using hsc⟩
  | (n, t) :: ys, hty, xs, h, sc, L, hsc, hnd => by
    rw [List.map_cons] at h
    obtain ⟨x, xs', rfl, hx, hxs⟩ := List.map_eq_cons_iff.mp h
    have hn : n ∉ L.map (·.1) := fun hm => by
      rw [List.map_append, List.nodup_append] at hnd
      exact hnd.2.2 n hm n (by simp) rfl
    obtain ⟨sc', h₁, h₂⟩ := define_defines (fun y hy => hty y (.tail _ hy)) xs' hxs
      (sc.insert n t) (L ++ [(n, t)]) (hsc.insert hn) (by simpa using hnd)
    refine ⟨sc', ?_, by simpa using h₂⟩
    simp only [define, decodeDef_eq hx (hty _ (.head _)), ok_bind, hsc.contains_eq_false hn,
      Bool.false_eq_true, ↓reduceIte, h₁]

/-- `defineBlocks` adds nothing for no blocks. -/
theorem defineBlocks_nil :
    Defines defineBlocks SBlock.eraseList (Block.treeList ([] : List (Block d)))
      (Block.scopeDefs ([] : List (Block d))) := by
  intro sbs h sc L hsc _
  rw [SBlock.eraseList_eq_nil h]
  exact ⟨sc, by simp only [defineBlocks] <;> rfl, by simpa [Block.scopeDefs] using hsc⟩

/-- `defineBlocks` adds a block's definitions and those of the blocks after
it, when `defineOps` adds the block's ops' and `defineBlocks` the other
blocks'. -/
theorem defineBlocks_cons {label : Name} {params : List (Name × d.Ty)}
    {body : List (Operation d)} {bs : List (Block d)}
    (hp : ∀ y ∈ params, decodeTy (tyAttr y.2) = some y.2)
    (hops : Defines defineOps SOp.eraseList (Operation.treeList body) (Operation.scopeDefs body))
    (hbs : Defines defineBlocks SBlock.eraseList (Block.treeList bs) (Block.scopeDefs bs)) :
    Defines defineBlocks SBlock.eraseList (Block.treeList (⟨label, params, body⟩ :: bs))
      (Block.scopeDefs (⟨label, params, body⟩ :: bs)) := by
  intro sbs h sc L hsc hnd
  obtain ⟨⟨_, ps, ops⟩, sbs', rfl, -, h₂, h₃, h₄⟩ := SBlock.eraseList_eq_cons h
  simp only [Block.scopeDefs] at hnd ⊢
  have hnd₁ : ((L ++ params ++ Operation.scopeDefs body ++ Block.scopeDefs bs).map (·.1)).Nodup :=
    by simpa only [List.append_assoc] using hnd
  obtain ⟨sc₁, e₁, k₁⟩ := define_defines hp ps h₂ sc L hsc (nodup_fst_left (nodup_fst_left hnd₁))
  obtain ⟨sc₂, e₂, k₂⟩ := hops ops h₃ sc₁ _ k₁ (nodup_fst_left hnd₁)
  obtain ⟨sc₃, e₃, k₃⟩ := hbs sbs' h₄ sc₂ _ k₂ hnd₁
  refine ⟨sc₃, ?_, by simpa only [List.append_assoc] using k₃⟩
  simp only [defineBlocks, e₁, ok_bind, e₂, e₃]

/-- `defineOps` adds nothing for no ops. -/
theorem defineOps_nil :
    Defines defineOps SOp.eraseList (Operation.treeList ([] : List (Operation d)))
      (Operation.scopeDefs ([] : List (Operation d))) := by
  intro sos h sc L hsc _
  rw [SOp.eraseList_eq_nil h]
  exact ⟨sc, by simp only [defineOps] <;> rfl, by simpa [Operation.scopeDefs] using hsc⟩

/-- `defineOps` adds an op's definitions and those of the ops after it,
when `defineRegions` adds the op's regions' and `defineOps` the other
ops'. -/
theorem defineOps_cons {results : List (Name × d.Ty)} {op : d.Op} {operands : List Name}
    {succs : List Succ} {regions : List (Region d)} {loc : LocRef} {os : List (Operation d)}
    (hr : ∀ y ∈ results, decodeTy (tyAttr y.2) = some y.2)
    (hreg : Defines defineRegions SRegion.eraseList (Region.treeList regions)
      (Region.scopeDefs regions))
    (hos : Defines defineOps SOp.eraseList (Operation.treeList os) (Operation.scopeDefs os)) :
    Defines defineOps SOp.eraseList
      (Operation.treeList (⟨results, op, operands, succs, regions, loc⟩ :: os))
      (Operation.scopeDefs (⟨results, op, operands, succs, regions, loc⟩ :: os)) := by
  intro sos h sc L hsc hnd
  obtain ⟨⟨sresults, _, _, _, _, _, sregions, _⟩, sos', rfl, h₁, h₂⟩ := SOp.eraseList_eq_cons h
  obtain ⟨hres, -, -, -, -, hregs, -⟩ := SOp.erase_eq_tree h₁
  simp only [Operation.scopeDefs] at hnd ⊢
  have hnd₁ :
      ((L ++ results ++ Region.scopeDefs regions ++ Operation.scopeDefs os).map (·.1)).Nodup := by
    simpa only [List.append_assoc] using hnd
  obtain ⟨sc₁, e₁, k₁⟩ := define_defines hr sresults hres sc L hsc
    (nodup_fst_left (nodup_fst_left hnd₁))
  obtain ⟨sc₂, e₂, k₂⟩ := hreg sregions hregs sc₁ _ k₁ (nodup_fst_left hnd₁)
  obtain ⟨sc₃, e₃, k₃⟩ := hos sos' h₂ sc₂ _ k₂ hnd₁
  refine ⟨sc₃, ?_, by simpa only [List.append_assoc] using k₃⟩
  simp only [defineOps, e₁, ok_bind, e₂, e₃]

/-- `defineRegions` adds nothing for no regions. -/
theorem defineRegions_nil :
    Defines defineRegions SRegion.eraseList (Region.treeList ([] : List (Region d)))
      (Region.scopeDefs ([] : List (Region d))) := by
  intro srs h sc L hsc _
  rw [SRegion.eraseList_eq_nil h]
  exact ⟨sc, by simp only [defineRegions] <;> rfl, by simpa [Region.scopeDefs] using hsc⟩

/-- `defineRegions` adds a region's definitions and those of the regions
after it, when `defineBlocks` adds the region's blocks' and
`defineRegions` the other regions'. -/
theorem defineRegions_cons {blocks : List (Block d)} {rs : List (Region d)}
    (hb : Defines defineBlocks SBlock.eraseList (Block.treeList blocks) (Block.scopeDefs blocks))
    (hrs : Defines defineRegions SRegion.eraseList (Region.treeList rs) (Region.scopeDefs rs)) :
    Defines defineRegions SRegion.eraseList (Region.treeList (⟨blocks⟩ :: rs))
      (Region.scopeDefs (⟨blocks⟩ :: rs)) := by
  intro srs h sc L hsc hnd
  obtain ⟨⟨sbs⟩, srs', rfl, h₁, h₂⟩ := SRegion.eraseList_eq_cons h
  simp only [Region.scopeDefs] at hnd ⊢
  have hnd₁ : ((L ++ Block.scopeDefs blocks ++ Region.scopeDefs rs).map (·.1)).Nodup := by
    simpa only [List.append_assoc] using hnd
  obtain ⟨sc₁, e₁, k₁⟩ := hb sbs h₁ sc L hsc (nodup_fst_left hnd₁)
  obtain ⟨sc₂, e₂, k₂⟩ := hrs srs' h₂ sc₁ _ k₁ hnd₁
  refine ⟨sc₂, ?_, by simpa only [List.append_assoc] using k₂⟩
  simp only [defineRegions, e₁, ok_bind, e₂]

end Fir.Text

namespace Fir

open Text

variable {d : Dialect} [DialectText d]

mutual
/-- `defineBlocks` adds the definitions of blocks, at any depth, when their
types decode. -/
theorem Block.defines : ∀ bs : List (Block d),
    (∀ y ∈ Block.scopeDefs bs, decodeTy (tyAttr y.2) = some y.2) →
    Defines defineBlocks SBlock.eraseList (Block.treeList bs) (Block.scopeDefs bs)
  | [], _ => defineBlocks_nil
  | ⟨label, params, body⟩ :: bs, hty =>
    defineBlocks_cons (fun y hy => hty y (by simp [Block.scopeDefs, hy]))
      (Operation.defines body fun y hy => hty y (by simp [Block.scopeDefs, hy]))
      (Block.defines bs fun y hy => hty y (by simp [Block.scopeDefs, hy]))

/-- `defineOps` adds the definitions of ops, at any depth, when their types
decode. -/
theorem Operation.defines : ∀ os : List (Operation d),
    (∀ y ∈ Operation.scopeDefs os, decodeTy (tyAttr y.2) = some y.2) →
    Defines defineOps SOp.eraseList (Operation.treeList os) (Operation.scopeDefs os)
  | [], _ => defineOps_nil
  | ⟨results, op, operands, succs, regions, loc⟩ :: os, hty =>
    defineOps_cons (fun y hy => hty y (by simp [Operation.scopeDefs, hy]))
      (Region.defines regions fun y hy => hty y (by simp [Operation.scopeDefs, hy]))
      (Operation.defines os fun y hy => hty y (by simp [Operation.scopeDefs, hy]))

/-- `defineRegions` adds the definitions of the blocks of regions, at any
depth, when their types decode. -/
theorem Region.defines : ∀ rs : List (Region d),
    (∀ y ∈ Region.scopeDefs rs, decodeTy (tyAttr y.2) = some y.2) →
    Defines defineRegions SRegion.eraseList (Region.treeList rs) (Region.scopeDefs rs)
  | [], _ => defineRegions_nil
  | ⟨blocks⟩ :: rs, hty =>
    defineRegions_cons (Block.defines blocks fun y hy => hty y (by simp [Region.scopeDefs, hy]))
      (Region.defines rs fun y hy => hty y (by simp [Region.scopeDefs, hy]))
end

variable [DialectSignature d]

/-- Every definition of a well-formed function has a type that decodes. -/
theorem Func.WellFormed.decodeTy_def {f : Func d} (hf : f.WellFormed) {y : Name × d.Ty}
    (hy : y ∈ f.defs) : decodeTy (tyAttr y.2) = some y.2 :=
  (hf.types y.2 (List.mem_append_right _ (List.mem_map_of_mem hy))).2

/-- The first pass, on the tree of a well-formed function: its parameters,
then its blocks, give a scope in which each value has the type that
`Func.typeOf` gives it. -/
theorem Func.WellFormed.scope {f : Func d} (hf : f.WellFormed) {sps : List SDef}
    {sbs : List SBlock} (hp : sps.map SDef.erase = f.params.map defTree)
    (hb : SBlock.eraseList sbs = Block.treeList f.blocks) :
    ∃ sc₁ sc, define ∅ sps = .ok sc₁ ∧ defineBlocks sc₁ sbs = .ok sc ∧
      ∀ x, sc[x]? = f.typeOf x := by
  have hperm := f.scopeDefs_perm
  have hnd : ((f.params ++ Block.scopeDefs f.blocks).map (·.1)).Nodup :=
    ((hperm.map _).nodup_iff).mpr hf.namesUnique
  have hty : ∀ y ∈ f.params ++ Block.scopeDefs f.blocks, decodeTy (tyAttr y.2) = some y.2 :=
    fun y hy => hf.decodeTy_def (hperm.mem_iff.mp hy)
  obtain ⟨sc₁, e₁, k₁⟩ := define_defines (ys := f.params)
    (fun y hy => hty y (List.mem_append_left _ hy)) sps hp ∅ [] Scope.holds_empty
    (by simpa using nodup_fst_left hnd)
  obtain ⟨sc₂, e₂, k₂⟩ := Block.defines f.blocks (fun y hy => hty y (List.mem_append_right _ hy))
    sbs hb sc₁ _ k₁ (by simpa using hnd)
  refine ⟨sc₁, sc₂, e₁, e₂, fun x => Option.ext fun t => ?_⟩
  rw [k₂ x t, Func.typeOf, find?_fst_eq_some hf.namesUnique]
  simpa using hperm.mem_iff (a := (x, t))

end Fir
