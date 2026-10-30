import Fir.Text.ReadLocs

/-!
# The syntax tree of a module

The proof that parsing a printed module gives the module back (#11) has one
step for each step of the parser. The first, `lex_print`, reads the printed
text as the module's tokens, `Module.tokens`. The second, in this section
and the ones after it, reads those tokens by the grammar: `readModule` gives
the module's own syntax tree, `Module.tree`, up to positions. The third
decodes that tree.

The tree of a module is how the grammar sees it. Each item is a `func` with
its symbol, its parameters, its result types and no attributes, and its body
is its blocks, `SBody.blocks`, even when it has none: a function's tokens
after its `{` start with a label or are its `}`, never a word, so `readItem`
reads its body as blocks. Each op is its results, its name and attributes as
the dialect writes them (`opName`, `opAttrs`), its operands, its successors,
its regions and its location reference. Each type is the attribute that
writes it, `tyAttr`. The location table is the module's own.

The tree that `readModule` gives holds the position of each part that
decoding can reject, taken from the tokens. A module has no positions, so
the tree of a module puts `TextPos.zero` at each of them, and `SModule.erase`
does the same to the tree that `readModule` gives. The reader's result is
stated as the equality of the two: `SModule.erase s = Module.tree m`.
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
  | ⟨bs⟩ :: rs => ⟨SBlock.eraseList bs⟩ :: SRegion.eraseList rs

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
  | .items is => .items (SItem.eraseList is)

/-- Items without their positions. -/
def SItem.eraseList : List SItem → List SItem
  | [] => []
  | i :: is => i.erase :: SItem.eraseList is
end

/-- A module's tree without its positions. -/
def SModule.erase (s : SModule) : SModule := ⟨SItem.eraseList s.items, s.locs⟩

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
  | ⟨blocks⟩ :: rs => ⟨Block.treeList blocks⟩ :: Region.treeList rs

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

/-- The tree of an item. -/
def Item.tree : Item d → SItem
  | .func f => f.tree

/-- The tree of a module: its items' trees and its location table. -/
def Module.tree (m : Module d) : SModule := ⟨m.items.map Item.tree, m.locs⟩

theorem Operation.treeList_eq_map :
    ∀ os : List (Operation d), Operation.treeList os = os.map Operation.tree
  | [] => rfl
  | o :: os => by rw [Operation.treeList, Operation.treeList_eq_map os, List.map_cons]

/-! # What a tree that erases to a module's tree holds

The decoding step starts from a tree that erases to a module's tree, and
these lemmas say what each of its parts holds.
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
    | items is => simp [SBody.erase] at h₇

/-- A module's tree, without positions, holds its items' trees and its
location table. -/
theorem SModule.erase_eq_tree {s : SModule} {m : Module d} (h : s.erase = m.tree) :
    s.items.map SItem.erase = m.items.map Item.tree ∧ s.locs = m.locs := by
  simpa [SModule.erase, Module.tree, SItem.eraseList_eq_map] using h

end Fir
