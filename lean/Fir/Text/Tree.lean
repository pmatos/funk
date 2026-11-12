import Fir.Text.ReadLocs

/-!
# The syntax tree of a module

The parser reads a text in three steps: the lexer reads it as tokens, the
grammar reads the tokens as a tree, and decoding turns the tree into a
module. The proof that parsing the printed text of a well-formed module
gives the module back has one step for each, and this section and the
eleven after it give the last two, and put all three together:

* Lexing printed text, in the sections before this one, reads the printed
  text of a module as exactly the module's tokens, then `eof`.
* The grammar step reads those tokens, at any positions, as the module's
  own tree, up to positions. This section defines that tree. The next
  seven read it back: what it means for a reader to read tokens back, then
  definitions and successors, ops, blocks and regions, a function, the
  location table, and the whole module.
* The decoding step gives the module back from any tree that is the
  module's tree up to positions. Three sections take it: the first pass,
  which builds the scope of a function; the second pass, which decodes its
  blocks and ops; and the module.
* The last section, the round trip, proved, puts the three steps together.

The tree of a module is how the grammar sees it. A function is a `func` with
its symbol, its parameters, its result types and no attributes, and its body
is its blocks, even when it has none: a function's tokens after its `{`
start with a label or are its `}`, never a word, so the grammar reads its
body as blocks. A nested module is a `module` with its symbol and no
parameters, results or attributes, and its body is its dialect set and its
items, or no blocks when it has neither, since its tokens after its `{` are
then its `}`. An item of a dialect's kind is an item of its kind with its
symbol, its parameters, its result types and its attributes, and its body
is no blocks. Each op is its results, its name and attributes as the
dialect writes them, its operands, its successors, its regions and its
location reference. Each type is the attribute that writes it, and so is
each entry of the data layout. The dialect set and the location table are
the module's own.

The tree that the grammar reads holds the position of each part that
decoding can reject, taken from the tokens. A module has no positions, so
the tree of a module puts the empty position at each of them, and erasing
the positions of the tree that the grammar reads does the same. The grammar
step is stated as the equality of the two.
-/

namespace Fir

/-- The position of every part of a tree without positions: line 0 and
column 0, where no text has a token, since both count from 1. -/
def TextPos.zero : TextPos := ⟨0, 0⟩

end Fir

namespace Fir.Text

/-! # Erasing positions -/

/-- A definition without its positions. -/
def SDef.erase (x : SDef) : SDef := ⟨x.name, .zero, x.ty, .zero⟩

/-- Something written at a position, without the position. -/
def eraseAt {α : Type} (x : α × TextPos) : α × TextPos := (x.1, .zero)

mutual
/-- An op without its positions, at any depth. -/
def SOp.erase : SOp → SOp
  | ⟨results, name, _, attrs, operands, succs, regions, loc⟩ =>
    ⟨results.map SDef.erase, name, .zero, attrs, operands.map eraseAt, succs,
      SRegion.eraseList regions, loc⟩

/-- Regions without their positions. -/
def SRegion.eraseList : List SRegion → List SRegion
  | [] => []
  | ⟨k, bs⟩ :: rs => ⟨k, SBlock.eraseList bs⟩ :: SRegion.eraseList rs

/-- Blocks without their positions. -/
def SBlock.eraseList : List SBlock → List SBlock
  | [] => []
  | ⟨label, params, ops⟩ :: bs =>
    ⟨label, params.map SDef.erase, SOp.eraseList ops⟩ :: SBlock.eraseList bs

/-- Ops without their positions. -/
def SOp.eraseList : List SOp → List SOp
  | [] => []
  | o :: os => o.erase :: SOp.eraseList os
end

mutual
/-- An item without its positions, at any depth. -/
def SItem.erase : SItem → SItem
  | ⟨kind, _, name, params, results, attrs, body⟩ =>
    ⟨kind, .zero, name, params.map SDef.erase, results.map eraseAt, attrs.map eraseAt,
      SBody.erase body⟩

/-- The body of an item without its positions. -/
def SBody.erase : SBody → SBody
  | .blocks bs => .blocks (SBlock.eraseList bs)
  | .items ds is => .items ds (SItem.eraseList is)

/-- Items without their positions. -/
def SItem.eraseList : List SItem → List SItem
  | [] => []
  | i :: is => i.erase :: SItem.eraseList is
end

/-- A module's tree without its positions. -/
def SModule.erase (s : SModule) : SModule :=
  ⟨s.dialects, s.layout.map eraseAt, SItem.eraseList s.items, s.locs⟩

theorem SOp.eraseList_eq_map : ∀ os : List SOp, SOp.eraseList os = os.map SOp.erase
  | [] => rfl
  | o :: os => by rw [SOp.eraseList, SOp.eraseList_eq_map os, List.map_cons]

theorem SItem.eraseList_eq_map : ∀ is : List SItem, SItem.eraseList is = is.map SItem.erase
  | [] => rfl
  | i :: is => by rw [SItem.eraseList, SItem.eraseList_eq_map is, List.map_cons]

end Fir.Text

namespace Fir

open Text

variable {d : Dialect} [DialectText d]

/-! # The tree of a module -/

/-- The tree of a definition: its name, and the attribute that writes its
type. -/
def defTree (x : Name × d.Ty) : SDef := ⟨x.1, .zero, tyAttr x.2, .zero⟩

mutual
/-- The tree of an op. -/
def Operation.tree : Operation d → SOp
  | ⟨results, op, operands, succs, regions, loc⟩ =>
    ⟨results.map defTree, opName op, .zero, opAttrs op, operands.map (·, .zero), succs,
      Region.treeList regions, loc⟩

/-- The trees of regions. -/
def Region.treeList : List (Region d) → List SRegion
  | [] => []
  | ⟨k, blocks⟩ :: rs => ⟨k, Block.treeList blocks⟩ :: Region.treeList rs

/-- The trees of blocks. -/
def Block.treeList : List (Block d) → List SBlock
  | [] => []
  | ⟨label, params, body⟩ :: bs =>
    ⟨label, params.map defTree, Operation.treeList body⟩ :: Block.treeList bs

/-- The trees of ops. -/
def Operation.treeList : List (Operation d) → List SOp
  | [] => []
  | o :: os => o.tree :: Operation.treeList os
end

/-- The tree of a function: an item of kind `func` with no attributes, whose
body is its blocks. -/
def Func.tree (f : Func d) : SItem :=
  ⟨"func", .zero, f.name, f.params.map defTree, f.results.map (tyAttr · , .zero), [],
    .blocks (Block.treeList f.body.blocks)⟩

/-- The body of a nested module: its dialect set and its items, or no
blocks when it has neither, as the grammar reads an empty body. -/
def moduleBody (ds : List Name) (is : List SItem) : SBody :=
  if ds.isEmpty ∧ is.isEmpty then .blocks [] else .items ds is

/-- The tree of an item of a dialect's kind: its kind, symbol, parameters,
results and attributes, and an empty body, which the grammar reads as no
blocks. -/
def DialectItem.tree (i : DialectItem d) : SItem :=
  ⟨i.kind, .zero, i.name, i.params.map defTree, i.results.map (tyAttr · , .zero),
    i.attrs.map (·, .zero), .blocks []⟩

mutual
/-- The tree of an item. A nested module is an item of kind `module` with no
parameters, results or attributes, whose body is its dialect set and its
items. -/
def Item.tree : Item d → SItem
  | .func f => f.tree
  | .module name ds is => ⟨"module", .zero, name, [], [], [], moduleBody ds (Item.treeList is)⟩
  | .dialect i => i.tree

/-- The trees of items. -/
def Item.treeList : List (Item d) → List SItem
  | [] => []
  | i :: is => i.tree :: Item.treeList is
end

theorem Item.treeList_eq_map : ∀ is : List (Item d), Item.treeList is = is.map Item.tree
  | [] => rfl
  | i :: is => by rw [Item.treeList, Item.treeList_eq_map is, List.map_cons]

/-- The tree of a module: its dialect set, the attributes that write its
layout's entries, its items' trees and its location table. -/
def Module.tree (m : Module d) : SModule :=
  ⟨m.dialects, m.layout.map (·.attr, .zero), m.items.map Item.tree, m.locs⟩

theorem Operation.treeList_eq_map :
    ∀ os : List (Operation d), Operation.treeList os = os.map Operation.tree
  | [] => rfl
  | o :: os => by rw [Operation.treeList, Operation.treeList_eq_map os, List.map_cons]

/-! # What a tree that erases to a module's tree holds

The decoding step starts from a tree that erases to a module's tree, and
these lemmas say what each of its parts holds: a definition, an op, a list
of ops, a list of blocks, a list of regions, an item and the module. Each
of the three lists has exactly as many elements as the module's, each
erasing to its counterpart's tree.
-/

/-- A definition that erases to a definition's tree names its value and
writes its type. -/
theorem SDef.erase_eq_defTree {x : SDef} {y : Name × d.Ty} :
    x.erase = defTree y ↔ x.name = y.1 ∧ x.ty = tyAttr y.2 := by
  obtain ⟨n, p, t, tp⟩ := x
  simp [SDef.erase, defTree]

/-- An op that erases to an op's tree holds the op's results, name,
attributes, operands, successors, regions and location reference. -/
theorem SOp.erase_eq_tree {so : SOp} {o : Operation d} (h : so.erase = o.tree) :
    so.results.map SDef.erase = o.results.map defTree ∧ so.name = opName o.op ∧
      so.attrs = opAttrs o.op ∧ so.operands.map (·.1) = o.operands ∧ so.succs = o.succs ∧
      SRegion.eraseList so.regions = Region.treeList o.regions ∧ so.loc = o.loc := by
  obtain ⟨results, name, namePos, attrs, operands, succs, regions, loc⟩ := so
  obtain ⟨results', op, operands', succs', regions', loc'⟩ := o
  simp only [SOp.erase, Operation.tree, SOp.mk.injEq] at h
  obtain ⟨h₁, h₂, -, h₄, h₅, h₆, h₇, h₈⟩ := h
  refine ⟨h₁, h₂, h₄, ?_, h₆, h₇, h₈⟩
  simpa [List.map_map, Function.comp_def, eraseAt] using congrArg (List.map Prod.fst) h₅

/-- No ops erase to the trees of no ops. -/
theorem SOp.eraseList_eq_nil {sos : List SOp}
    (h : SOp.eraseList sos = Operation.treeList ([] : List (Operation d))) : sos = [] := by
  cases sos with
  | nil => rfl
  | cons _ _ => simp [SOp.eraseList, Operation.treeList] at h

/-- Ops that erase to the trees of an op and the ops after it are an op
that erases to the op's tree, then ops that erase to the others' trees. -/
theorem SOp.eraseList_eq_cons {sos : List SOp} {o : Operation d} {os : List (Operation d)}
    (h : SOp.eraseList sos = Operation.treeList (o :: os)) :
    ∃ so sos', sos = so :: sos' ∧ so.erase = o.tree ∧
      SOp.eraseList sos' = Operation.treeList os := by
  cases sos with
  | nil => simp [SOp.eraseList, Operation.treeList] at h
  | cons so sos' =>
    simp only [SOp.eraseList, Operation.treeList, List.cons.injEq] at h
    exact ⟨so, sos', rfl, h.1, h.2⟩

/-- No blocks erase to the trees of no blocks. -/
theorem SBlock.eraseList_eq_nil {sbs : List SBlock}
    (h : SBlock.eraseList sbs = Block.treeList ([] : List (Block d))) : sbs = [] := by
  cases sbs with
  | nil => rfl
  | cons sb _ =>
    obtain ⟨_, _, _⟩ := sb
    simp [SBlock.eraseList, Block.treeList] at h

/-- Blocks that erase to the trees of a block and the blocks after it are a
block with the block's label, with arguments and ops that erase to the
block's, then blocks that erase to the others' trees. -/
theorem SBlock.eraseList_eq_cons {sbs : List SBlock} {b : Block d} {bs : List (Block d)}
    (h : SBlock.eraseList sbs = Block.treeList (b :: bs)) :
    ∃ sb sbs', sbs = sb :: sbs' ∧ sb.label = b.label ∧
      sb.params.map SDef.erase = b.params.map defTree ∧
      SOp.eraseList sb.ops = Operation.treeList b.body ∧
      SBlock.eraseList sbs' = Block.treeList bs := by
  obtain ⟨label, params, body⟩ := b
  cases sbs with
  | nil => simp [SBlock.eraseList, Block.treeList] at h
  | cons sb sbs' =>
    obtain ⟨label', params', ops⟩ := sb
    simp only [SBlock.eraseList, Block.treeList, List.cons.injEq, SBlock.mk.injEq] at h
    obtain ⟨⟨h₁, h₂, h₃⟩, h₄⟩ := h
    exact ⟨_, sbs', rfl, h₁, h₂, h₃, h₄⟩

/-- No regions erase to the trees of no regions. -/
theorem SRegion.eraseList_eq_nil {srs : List SRegion}
    (h : SRegion.eraseList srs = Region.treeList ([] : List (Region d))) : srs = [] := by
  cases srs with
  | nil => rfl
  | cons sr _ =>
    obtain ⟨_⟩ := sr
    simp [SRegion.eraseList, Region.treeList] at h

/-- Regions that erase to the trees of a region and the regions after it
are a region of the region's kind whose blocks erase to the region's, then
regions that erase to the others' trees. -/
theorem SRegion.eraseList_eq_cons {srs : List SRegion} {r : Region d} {rs : List (Region d)}
    (h : SRegion.eraseList srs = Region.treeList (r :: rs)) :
    ∃ sr srs', srs = sr :: srs' ∧ sr.kind = r.kind ∧
      SBlock.eraseList sr.blocks = Block.treeList r.blocks ∧
      SRegion.eraseList srs' = Region.treeList rs := by
  obtain ⟨kind, blocks⟩ := r
  cases srs with
  | nil => simp [SRegion.eraseList, Region.treeList] at h
  | cons sr srs' =>
    obtain ⟨k, bs⟩ := sr
    simp only [SRegion.eraseList, Region.treeList, List.cons.injEq, SRegion.mk.injEq] at h
    exact ⟨_, srs', rfl, h.1.1, h.1.2, h.2⟩

/-- An item that erases to a function's tree is a `func` with the
function's symbol, parameters and result types, no attributes, and the
function's blocks as its body. -/
theorem SItem.erase_eq_funcTree {si : SItem} {f : Func d} (h : si.erase = f.tree) :
    si.kind = "func" ∧ si.name = f.name ∧ si.params.map SDef.erase = f.params.map defTree ∧
      si.results.map (·.1) = f.results.map tyAttr ∧ si.attrs = [] ∧
      ∃ bs, si.body = .blocks bs ∧ SBlock.eraseList bs = Block.treeList f.body.blocks := by
  obtain ⟨kind, kindPos, name, params, results, attrs, body⟩ := si
  simp only [SItem.erase, Func.tree, SItem.mk.injEq] at h
  obtain ⟨h₁, -, h₃, h₄, h₅, h₆, h₇⟩ := h
  refine ⟨h₁, h₃, h₄, ?_, by simpa using h₆, ?_⟩
  · simpa [List.map_map, Function.comp_def, eraseAt] using congrArg (List.map Prod.fst) h₅
  · cases body with
    | blocks bs => exact ⟨bs, rfl, by simpa [SBody.erase] using h₇⟩
    | items _ _ => simp [SBody.erase] at h₇

/-- A module's tree, without positions, holds its dialect set, what its layout's
entries write, its items' trees and its location table. -/
theorem SModule.erase_eq_tree {s : SModule} {m : Module d} (h : s.erase = m.tree) :
    s.dialects = m.dialects ∧ s.layout.map Prod.fst = m.layout.map MemLayout.attr ∧
      s.items.map SItem.erase = m.items.map Item.tree ∧ s.locs = m.locs := by
  simp only [SModule.erase, Module.tree, SModule.mk.injEq, SItem.eraseList_eq_map] at h
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  refine ⟨h₁, ?_, h₃, h₄⟩
  simpa [List.map_map, Function.comp_def, eraseAt] using congrArg (List.map Prod.fst) h₂

end Fir
