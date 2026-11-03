import Fir.Text.DecodeBlocks

/-!
# Decoding the tree of a module

A module's tree decodes item by item, and each item of a module's tree is a
`func` with no attributes whose body is its blocks. So `decodeItem` takes
its branch for blocks, the only one that printed text reaches: `readModule`
reads every function body of a printed module as `SBody.blocks`, the empty
`{ }` included, never as `SBody.items []`. `decodeFunc` then decodes the
result types, builds the scope with the first pass, decodes the parameters,
and decodes the blocks in the scope with the second pass.

The result is `Module.WellFormed.decodeModule_eq`: on any tree that erases
to the tree of a well-formed module, at any positions, `decodeModule` gives
the module back. Decoding reads positions only to report errors, and the
tree of a well-formed module has none.
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
  · simp only [e₁, ok_bind, e₂, hps, hbs]
    obtain ⟨_, _, _, ⟨_⟩⟩ := f
    rfl

/-- An item decodes back from a tree that erases to its tree, when its
function is well formed. -/
theorem Func.WellFormed.decodeItem_eq {f : Func d} (hf : f.WellFormed) {si : SItem}
    (h : si.erase = f.tree) : Text.decodeItem si = .ok (.func f) := by
  obtain ⟨hk, hn, hp, hr, ha, bs, hb, hbs⟩ := SItem.erase_eq_funcTree h
  obtain ⟨kind, kindPos, name, params, results, attrs, body⟩ := si
  dsimp only at hk hn hp hr ha hb
  subst hk hn ha hb
  simp only [Text.decodeItem, ne_eq, not_true_eq_false, ↓reduceIte, hf.decodeFunc_eq hp hr hbs,
    ok_bind]
  rfl

/-- The items of a module decode back from trees that erase to their trees,
when each of its functions is well formed. -/
theorem mapM_decodeItem : ∀ {sis : List SItem} {items : List (Item d)},
    (∀ f, Item.func f ∈ items → f.WellFormed) → sis.map SItem.erase = items.map Item.tree →
      sis.mapM Text.decodeItem = .ok items
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | si :: sis, .func f :: items, hw, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.mapM_cons, (hw f (.head _)).decodeItem_eq h.1, ok_bind,
      mapM_decodeItem (fun f' hf' => hw f' (.tail _ hf')) h.2] <;> rfl

/-- The decoding step: on any tree that erases to the tree of a well-formed
module, at any positions, `decodeModule` gives the module back. -/
theorem Module.WellFormed.decodeModule_eq {m : Module d} (hm : m.WellFormed) {s : SModule}
    (h : s.erase = m.tree) : Text.decodeModule s = .ok m := by
  obtain ⟨hi, hl⟩ := SModule.erase_eq_tree h
  have hw : ∀ f, Item.func f ∈ m.items → f.WellFormed := fun f hf =>
    hm.funcs f (List.mem_map.mpr ⟨_, hf, rfl⟩)
  simp only [Text.decodeModule, mapM_decodeItem hw hi, ok_bind, hl]
  rfl

end Fir
