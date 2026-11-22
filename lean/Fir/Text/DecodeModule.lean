import Fir.Text.DecodeFuncItem
import Fir.Text.GlobalLaws

/-!
# Decoding the tree of a module

A module's tree decodes its data layout entry by entry, each entry from the
attribute it writes, and then item by item. A function's item is a `func` with no
attributes whose body is its blocks. So the decoder of items takes its
branch for blocks, the only one that printed text reaches: the grammar reads
every function body of a printed module as blocks, the empty `{ }` included,
never as an empty list of items. A nested module's item is a `module` with
no parameters, results or attributes, whose body is its dialect set and its
items, or no blocks when it has neither, and it decodes its items in turn.
An item of a dialect's kind has a word of a dialect as its kind, so it is
neither a `func`, a `module`, an `aggregate`, a `global` nor an `extern`, and its empty
body reads as no blocks. An aggregate's layout decodes back from the
attributes it writes when its numbers are within the limit and its fields'
types decode back, and a global when its numbers are within the limit.
Decoding a function then decodes the result types, builds the scope with
the first pass, decodes the parameters, and decodes the blocks in the scope
with the second pass.

The result is the decoding step: on any tree that erases to the tree of a
well-formed module, at any positions, decoding gives the module back.
Decoding reads positions only to report errors, and on the tree of a
well-formed module it reports none.
-/

namespace Fir

open Text

variable {d : Dialect} [DialectText d]

variable [DialectSignature d] [DialectValidation d] [LawfulDialectText d]

omit [DialectText d] [DialectSignature d] [DialectValidation d] [LawfulDialectText d] in
/-- Lists of attributes that erase to empty lists are empty. -/
theorem nil_of_map_erase {α : Type} {pas : List (List (Attr × TextPos))} {ys : List α}
    (h : pas.map (·.map eraseAt) = ys.map fun _ => []) : ∀ as ∈ pas, as = [] := by
  intro as has
  have hm : as.map eraseAt ∈ ys.map (fun _ => ([] : List (Attr × TextPos))) :=
    h ▸ List.mem_map_of_mem has
  obtain ⟨_, -, he⟩ := List.mem_map.mp hm
  exact List.map_eq_nil_iff.mp he.symm

omit [DialectText d] [DialectSignature d] [DialectValidation d] [LawfulDialectText d] in
/-- The header of an item other than a `func` passes when no parameter or
result carries attributes and the parameters do not end in `...`. -/
theorem plainHeader_eq {pas ras : List (List (Attr × TextPos))} {v : Option TextPos}
    (hp : ∀ as ∈ pas, as = []) (hv : v.map (fun _ => TextPos.zero) = none)
    (hr : ∀ as ∈ ras, as = []) : plainHeader pas v ras = .ok () := by
  have h₁ : pas.flatten = [] := List.flatten_eq_nil_iff.mpr hp
  have h₂ : ras.flatten = [] := List.flatten_eq_nil_iff.mpr hr
  obtain rfl : v = none := Option.map_eq_none_iff.mp hv
  unfold plainHeader
  rw [h₁, h₂]
  rfl

/-- A word of a dialect is not the kind `func`, `module`, `aggregate`, `global`
or `extern`. -/
theorem isDialectWord_ne {k : String} (hk : isDialectWord k) :
    k ≠ "func" ∧ k ≠ "module" ∧ k ≠ "aggregate" ∧ k ≠ "global" ∧ k ≠ "extern" :=
  ⟨by rintro rfl; exact absurd hk (by decide), by rintro rfl; exact absurd hk (by decide),
    by rintro rfl; exact absurd hk (by decide), by rintro rfl; exact absurd hk (by decide),
    by rintro rfl; exact absurd hk (by decide)⟩

omit [DialectSignature d] [DialectValidation d] [LawfulDialectText d] in
/-- An item of a dialect's kind decodes back from a tree that erases to its
tree, at any positions, when it is well formed. -/
theorem DialectItem.WellFormed.decodeItem_eq {i : DialectItem d} (hi : i.WellFormed)
    {si : SItem} (h : si.erase = i.tree) : Text.decodeItem si = .ok (.dialect i) := by
  obtain ⟨kind, kindPos, name, params, paramAttrs, variadic, results, resultAttrs, attrs, body⟩ :=
    si
  simp only [SItem.erase, DialectItem.tree, SItem.mk.injEq] at h
  obtain ⟨rfl, -, rfl, hp, hpa, hv, hr, hra, ha, hb⟩ := h
  have hph := plainHeader_eq (nil_of_map_erase hpa) hv (nil_of_map_erase hra)
  obtain rfl : body = .blocks [] := by
    cases body with
    | blocks bs =>
      cases bs with
      | nil => rfl
      | cons b _ => obtain ⟨⟩ := b; simp [SBody.erase, SBlock.eraseList] at hb
    | items => simp [SBody.erase] at hb
  have hr' : results.map (·.1) = i.results.map tyAttr := by
    simpa [List.map_map, Function.comp_def, eraseAt] using congrArg (List.map Prod.fst) hr
  have ha' : attrs.map (·.1) = i.attrs := by
    simpa [List.map_map, Function.comp_def, eraseAt] using congrArg (List.map Prod.fst) ha
  have hty : ∀ t ∈ i.types, decodeTy (tyAttr t) = some t := fun t ht => (hi.types t ht).2
  have hres : results.mapM (fun (a, p) => decodeType (d := d) a p) = .ok i.results :=
    mapM_decodeType (fun _ _ => rfl) hr' fun t ht => hty t (List.mem_append_right _ ht)
  have hps : params.mapM decodeDef = .ok i.params := mapM_decodeDef hp fun y hy =>
    hty y.2 (List.mem_append_left _ (List.mem_map_of_mem hy))
  obtain ⟨hf, hm, hg, hgl, hx⟩ := isDialectWord_ne hi.kind
  rw [Text.decodeItem.eq_def]
  simp only [hf, hm, hg, hgl, hx, hi.kind, ↓reduceIte, hph, ok_bind, decodeDialectItem, hres, hps, ha']
  rfl

omit [DialectSignature d] [DialectValidation d] [LawfulDialectText d] in
/-- Fields decode back from the attributes they write, at any positions,
when their numbers are within the limit and their types are written as
types and decode back. -/
theorem decodeFields_eq : ∀ {fs : List (Field d)}, (∀ f ∈ fs, f.offset ≤ Aggregate.limit ∧
      (∀ c ∈ f.count, c ≤ Aggregate.limit) ∧ (tyAttr f.ty).IsType ∧
        decodeTy (tyAttr f.ty) = some f.ty) →
    ∀ {ss : List (Attr × TextPos)}, ss.map Prod.fst = fs.map Field.attr →
      ss.mapM Text.decodeField = .ok fs
  | [], _, [], _ => rfl
  | [], _, _ :: _, h => by simp at h
  | _ :: _, _, [], h => by simp at h
  | f :: fs, hw, (a, p) :: ss, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hw f (List.mem_cons_self ..)
    rw [List.mapM_cons]
    simp only [Text.decodeField, Field.decode_attr h₁ h₂ h₃ h₄]
    rw [decodeFields_eq (fun x hx => hw x (List.mem_cons_of_mem _ hx)) h]
    rfl

omit [DialectSignature d] [DialectValidation d] [LawfulDialectText d] in
/-- An aggregate's layout decodes back from a tree that erases to its tree,
at any positions, when it is well formed. -/
theorem Aggregate.WellFormed.decodeItem_eq {a : Aggregate d} (ha : a.WellFormed)
    {si : SItem} (h : si.erase = a.item.tree) : Text.decodeItem si = .ok (.aggregate a) := by
  obtain ⟨kind, kindPos, name, params, paramAttrs, variadic, results, resultAttrs, attrs, body⟩ :=
    si
  simp only [SItem.erase, DialectItem.tree, Aggregate.item, SItem.mk.injEq] at h
  obtain ⟨rfl, -, rfl, hp, hpa, hv, hr, hra, hA, hb⟩ := h
  have hph := plainHeader_eq (nil_of_map_erase hpa) hv (nil_of_map_erase hra)
  obtain rfl : params = [] := List.map_eq_nil_iff.mp hp
  obtain rfl : results = [] := List.map_eq_nil_iff.mp hr
  obtain rfl : body = .blocks [] := by
    cases body with
    | blocks bs =>
      cases bs with
      | nil => rfl
      | cons b _ => obtain ⟨⟩ := b; simp [SBody.erase, SBlock.eraseList] at hb
    | items => simp [SBody.erase] at hb
  have hA' : attrs.map (·.1) = a.attrs := by
    simpa [List.map_map, Function.comp_def, eraseAt] using congrArg (List.map Prod.fst) hA
  obtain ⟨⟨hm, hs, hal, hfl⟩, hty⟩ := ha
  have hfs : ∀ f ∈ a.fields, f.offset ≤ Aggregate.limit ∧ (∀ c ∈ f.count, c ≤ Aggregate.limit) ∧
      (tyAttr f.ty).IsType ∧ decodeTy (tyAttr f.ty) = some f.ty := fun f hf =>
    ⟨(hfl f hf).1, (hfl f hf).2, hty f.ty (List.mem_map_of_mem hf)⟩
  match attrs, hA' with
  | (m, pm) :: (s, ps) :: (al, pa) :: fs, hA' =>
    simp only [Aggregate.attrs, List.map_cons, List.cons.injEq] at hA'
    obtain ⟨rfl, rfl, rfl, hF⟩ := hA'
    rw [Text.decodeItem.eq_def]
    simp only [String.reduceEq, ↓reduceIte, hph, ok_bind, decodeAggregate,
      Aggregate.decodeNumber_app _ hm,
      Aggregate.decodeNumber_app _ hs, Aggregate.decodeNumber_app _ hal, decodeFields_eq hfs hF,
      ok_bind]
    rfl

omit [DialectSignature d] [DialectValidation d] [LawfulDialectText d] in
/-- A global decodes back from a tree that erases to its tree, at any
positions, when its numbers are within the limit. -/
theorem Global.decodeItem_eq {g : Global} (hg : g.InLimits) {si : SItem}
    (h : si.erase = (g.item (d := d)).tree) : Text.decodeItem (d := d) si = .ok (.global g) := by
  obtain ⟨kind, kindPos, name, params, paramAttrs, variadic, results, resultAttrs, attrs, body⟩ :=
    si
  simp only [SItem.erase, DialectItem.tree, Global.item, SItem.mk.injEq] at h
  obtain ⟨rfl, -, rfl, hp, hpa, hv, hr, hra, hA, hb⟩ := h
  have hph := plainHeader_eq (nil_of_map_erase hpa) hv (nil_of_map_erase hra)
  obtain rfl : params = [] := List.map_eq_nil_iff.mp hp
  obtain rfl : results = [] := List.map_eq_nil_iff.mp hr
  obtain rfl : body = .blocks [] := by
    cases body with
    | blocks bs =>
      cases bs with
      | nil => rfl
      | cons b _ => obtain ⟨⟩ := b; simp [SBody.erase, SBlock.eraseList] at hb
    | items => simp [SBody.erase] at hb
  have hA' : attrs.map (·.1) = g.attrs := by
    simpa [List.map_map, Function.comp_def, eraseAt] using congrArg (List.map Prod.fst) hA
  rw [Text.decodeItem.eq_def]
  simp only [String.reduceEq, ↓reduceIte, hph, ok_bind, decodeGlobal, hA',
    Global.decodeAttrs_attrs hg]
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
  | .dialect _, hi, _, h => DialectItem.WellFormed.decodeItem_eq hi h
  | .aggregate _, ha, _, h => Aggregate.WellFormed.decodeItem_eq ha h
  | .global _, hg, _, h => Global.decodeItem_eq hg h
  | .extern _, he, _, h => Extern.decodeItem_eq he h
  | .module name ds is, hm,
      ⟨kind, kindPos, sname, params, paramAttrs, variadic, results, resultAttrs, attrs, body⟩, h => by
    simp only [SItem.erase, Item.tree, SItem.mk.injEq] at h
    obtain ⟨rfl, -, rfl, hp, hpa, hv, hr, hra, ha, hb⟩ := h
    obtain rfl : paramAttrs = [] := List.map_eq_nil_iff.mp hpa
    obtain rfl : variadic = none := Option.map_eq_none_iff.mp hv
    obtain rfl : resultAttrs = [] := List.map_eq_nil_iff.mp hra
    obtain rfl : params = [] := List.map_eq_nil_iff.mp hp
    obtain rfl : results = [] := List.map_eq_nil_iff.mp hr
    obtain rfl : attrs = [] := List.map_eq_nil_iff.mp ha
    rw [Text.decodeItem.eq_def]
    simp only [String.reduceEq, ↓reduceIte, plainHeader, List.flatten_nil, moduleHeader]
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

/-- The entries of a data layout decode back from the attributes they write,
at any positions, when their numbers are within the limit. -/
theorem decodeLayout_eq : ∀ {es : List MemLayout}, (∀ e ∈ es, e.InLimits) →
    ∀ {ss : List (Attr × TextPos)}, ss.map Prod.fst = es.map MemLayout.attr →
      ss.mapM Text.decodeMemLayout = .ok es
  | [], _, [], _ => rfl
  | [], _, _ :: _, h => by simp at h
  | _ :: _, _, [], h => by simp at h
  | e :: es, hw, (a, p) :: ss, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    rw [List.mapM_cons]
    simp only [Text.decodeMemLayout, MemLayout.decode_attr (hw e (List.mem_cons_self ..))]
    rw [decodeLayout_eq (fun x hx => hw x (List.mem_cons_of_mem _ hx)) h]
    rfl

/-- The decoding step: on any tree that erases to the tree of a well-formed
module, at any positions, `decodeModule` gives the module back. -/
theorem Module.WellFormed.decodeModule_eq {m : Module d} (hm : m.WellFormed) {s : SModule}
    (h : s.erase = m.tree) : Text.decodeModule s = .ok m := by
  obtain ⟨hn, hL, hi, hl⟩ := SModule.erase_eq_tree h
  rw [← SItem.eraseList_eq_map, ← Item.treeList_eq_map] at hi
  have hw := Item.WellFormed.decodeItems_eq ((Item.wellFormedList_iff _).mpr hm.items) hi
  rw [decodeItems_eq_mapM] at hw
  simp only [Text.decodeModule, decodeLayout_eq hm.layout hL, hw, ok_bind, hl, hn]
  rfl

end Fir
