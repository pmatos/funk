import Fir.Text.DecodeBlocks

/-!
# Decoding the tree of a module

A module's tree decodes item by item. A function's item is a `func` with no
attributes whose body is its blocks. So the decoder of items takes its
branch for blocks, the only one that printed text reaches: the grammar reads
every function body of a printed module as blocks, the empty `{ }` included,
never as an empty list of items. A nested module's item is a `module` with
no parameters, results or attributes, whose body is its dialect set and its
items, or no blocks when it has neither, and it decodes its items in turn.
Decoding a function then
decodes the result types, builds the scope with the first pass, decodes the
parameters, and decodes the blocks in the scope with the second pass.

The result is the decoding step: on any tree that erases to the tree of a
well-formed module, at any positions, decoding gives the module back.
Decoding reads positions only to report errors, and on the tree of a
well-formed module it reports none.
-/

namespace Fir

open Text

variable {d : Dialect} [DialectText d]

/-- Binding a result that a step gives runs what follows on it. -/
theorem bind_eq_of {ε α β : Type} {x : Except ε α} {a : α} {k : α → Except ε β}
    (h : x = .ok a) : (x >>= k) = k a := by
  subst h
  rfl

/-- The result types of a function's tree decode as the function's result
types, when each decodes back to itself. -/
theorem mapM_decodeType {g : Attr × TextPos → Except ParseError d.Ty}
    (hg : ∀ a p, g (a, p) = decodeType a p) :
    ∀ {as : List (Attr × TextPos)} {ts : List d.Ty}, as.map (·.1) = ts.map tyAttr →
      (∀ t ∈ ts, decodeTy (tyAttr t) = some t) → as.mapM g = .ok ts
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | (a, p) :: as, t :: ts, h, ht => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have hx : g (tyAttr t, p) = .ok t := by
      rw [hg]
      simp only [decodeType, ht t (.head _)]
    simp only [List.mapM_cons, hx, ok_bind,
      mapM_decodeType hg h fun t' ht' => ht t' (.tail _ ht')] <;> rfl

variable [DialectSignature d] [DialectValidation d] [LawfulDialectText d]

/-- A function decodes back from its tree, at any positions, when it is
well formed. -/
theorem Func.WellFormed.decodeFunc_eq {f : Func d} (hf : f.WellFormed) {sps : List SDef}
    {srs : List (Attr × TextPos)} {sbs : List SBlock}
    (hp : sps.map SDef.erase = f.params.map defTree) (hr : srs.map (·.1) = f.results.map tyAttr)
    (hb : SBlock.eraseList sbs = Block.treeList f.body.blocks) :
    Text.decodeFunc f.name sps srs sbs = .ok f := by
  obtain ⟨sc₁, sc, e₁, e₂, hsc⟩ := hf.scope hp hb
  have hps : sps.mapM decodeDef = .ok f.params :=
    mapM_decodeDef hp fun y hy => hf.decodeTy_def (List.mem_append_left _ hy)
  have hbs := Block.decodesList sc f.name f.body.blocks (hf.decodesIn hsc) sbs hb
  unfold Text.decodeFunc
  refine (bind_eq_of (a := f.results) ?_).trans ?_
  · exact mapM_decodeType (fun _ _ => rfl) hr fun t ht =>
      (hf.types t (List.mem_append_left _ ht)).2
  · have hk := hf.bodyKind
    simp only [e₁, ok_bind, e₂, hps, hbs]
    obtain ⟨_, _, _, ⟨_, _⟩⟩ := f
    simp only at hk
    subst hk
    rfl

/-- A function's item decodes back from a tree that erases to its tree, when
the function is well formed. -/
theorem Func.WellFormed.decodeItem_eq {f : Func d} (hf : f.WellFormed) {si : SItem}
    (h : si.erase = f.tree) : Text.decodeItem si = .ok (.func f) := by
  obtain ⟨hk, hn, hp, hr, ha, bs, hb, hbs⟩ := SItem.erase_eq_funcTree h
  obtain ⟨kind, kindPos, name, params, results, attrs, body⟩ := si
  dsimp only at hk hn hp hr ha hb
  subst hk hn ha hb
  rw [Text.decodeItem.eq_def]
  simp only [↓reduceIte, decodeFuncItem, hf.decodeFunc_eq hp hr hbs]
  rfl

-- The two theorems recurse together, so both take the dialect's lawful
-- text, which only the first states it needs.
set_option linter.unusedSectionVars false in
mutual
/-- An item decodes back from a tree that erases to its tree, at any
positions, when it is well formed. -/
theorem Item.WellFormed.decodeItem_eq : ∀ {i : Item d}, i.WellFormed → ∀ {si : SItem},
    si.erase = i.tree → Text.decodeItem si = .ok i
  | .func _, hf, _, h => Func.WellFormed.decodeItem_eq hf h
  | .module name ds is, hm, ⟨kind, kindPos, sname, params, results, attrs, body⟩, h => by
    simp only [SItem.erase, Item.tree, SItem.mk.injEq] at h
    obtain ⟨rfl, -, rfl, hp, hr, ha, hb⟩ := h
    obtain rfl : params = [] := List.map_eq_nil_iff.mp hp
    obtain rfl : results = [] := List.map_eq_nil_iff.mp hr
    obtain rfl : attrs = [] := List.map_eq_nil_iff.mp ha
    rw [Text.decodeItem.eq_def]
    simp only [String.reduceEq, ↓reduceIte, moduleHeader]
    by_cases he : ds.isEmpty = true ∧ (Item.treeList is).isEmpty = true
    · simp only [moduleBody, he, and_self, ite_true] at hb
      obtain ⟨hd, hi⟩ := he
      rw [List.isEmpty_iff] at hd hi
      subst hd
      obtain rfl : is = [] := by
        cases is with
        | nil => rfl
        | cons => simp [Item.treeList] at hi
      cases body with
      | blocks bs =>
        obtain rfl : bs = [] := by
          cases bs with
          | nil => rfl
          | cons b _ =>
            obtain ⟨⟩ := b
            simp [SBody.erase, SBlock.eraseList] at hb
        rfl
      | items => simp [SBody.erase] at hb
    · simp only [moduleBody, he, ite_false] at hb
      cases body with
      | blocks => simp [SBody.erase] at hb
      | items ds' sis =>
        simp only [SBody.erase, SBody.items.injEq] at hb
        obtain ⟨rfl, hb⟩ := hb
        simp only [Item.WellFormed.decodeItems_eq hm.2 hb, ok_bind]
        rfl

/-- Items decode back from trees that erase to their trees, at any
positions, when each is well formed. -/
theorem Item.WellFormed.decodeItems_eq : ∀ {is : List (Item d)}, Item.WellFormedList is →
    ∀ {sis : List SItem}, SItem.eraseList sis = Item.treeList is → Text.decodeItems sis = .ok is
  | [], _, [], _ => rfl
  | [], _, _ :: _, h => by simp [SItem.eraseList, Item.treeList] at h
  | _ :: _, _, [], h => by simp [SItem.eraseList, Item.treeList] at h
  | _ :: _, hw, _ :: _, h => by
    simp only [SItem.eraseList, Item.treeList, List.cons.injEq] at h
    rw [Text.decodeItems.eq_def]
    dsimp only
    rw [Item.WellFormed.decodeItem_eq hw.1 h.1, ok_bind,
      Item.WellFormed.decodeItems_eq hw.2 h.2]
    rfl
end

/-- The decoding step: on any tree that erases to the tree of a well-formed
module, at any positions, `decodeModule` gives the module back. -/
theorem Module.WellFormed.decodeModule_eq {m : Module d} (hm : m.WellFormed) {s : SModule}
    (h : s.erase = m.tree) : Text.decodeModule s = .ok m := by
  obtain ⟨hn, hi, hl⟩ := SModule.erase_eq_tree h
  rw [← SItem.eraseList_eq_map, ← Item.treeList_eq_map] at hi
  have hw := Item.WellFormed.decodeItems_eq ((Item.wellFormedList_iff _).mpr hm.items) hi
  rw [decodeItems_eq_mapM] at hw
  simp only [Text.decodeModule, hw, ok_bind, hl, hn]
  rfl

end Fir
