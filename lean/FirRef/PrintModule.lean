import FirRef.PrintAttr

/-!
`fir-ref` prints modules with `printModule`, not with the spec's
`Module.print`. The spec's printer recurses once per level of regions, and
each `printList` builds the text of a list's head and then copies the text
of its tail after it, so it takes time quadratic in the length of a block
and cubic in the depth of regions. `printModule` keeps what is left to
print on an explicit stack of frames and appends each piece of text to one
accumulator: it takes no stack per level and runs in time linear in the
text it writes. The theorem `print_eq_printModule` proves the two equal,
and `@[csimp]` makes Lean compile every later call of `Module.print` as a
call of `printModule` (ADR-2026-10-30-1450).

This module comes after `FirRef.PrintAttr`, so the attributes and types
that it prints go through `printAttr`. It prints definitions with its own
copies of `printDef` and `printDefs`: the spec's are compiled before
`print_eq_printAttr`, so they print types with the spec's `Attr.print`.
-/

namespace FirRef

open Fir Fir.Text

variable {d : Dialect}

/-- What is left to print of a module. -/
inductive Frame (d : Dialect) where
  /-- Text. -/
  | str (s : String)
  /-- Ops at an indentation. -/
  | ops (n : Nat) (os : List (Operation d))
  /-- Blocks at an indentation. -/
  | blocks (n : Nat) (bs : List (Block d))
  /-- The regions of an op at an indentation. -/
  | regions (n : Nat) (rs : List (Region d))
  /-- Items, each followed by an empty line. -/
  | items (is : List (Item d))

mutual
/-- A measure of an op that each step of `printFrames` lowers. -/
def opWeight : Operation d → Nat
  | ⟨_, _, _, _, rs, _⟩ => regionsWeight rs + 1

/-- A measure of ops. -/
def opsWeight : List (Operation d) → Nat
  | [] => 0
  | o :: os => opWeight o + opsWeight os + 3

/-- A measure of blocks. -/
def blocksWeight : List (Block d) → Nat
  | [] => 0
  | ⟨_, _, os⟩ :: bs => opsWeight os + blocksWeight bs + 3

/-- A measure of regions. -/
def regionsWeight : List (Region d) → Nat
  | [] => 0
  | ⟨bs⟩ :: rs => blocksWeight bs + regionsWeight rs + 3
end

/-- A measure of items. -/
def itemsWeight : List (Item d) → Nat
  | [] => 0
  | .func f :: is => blocksWeight f.body.blocks + itemsWeight is + 4

/-- A measure of a frame. -/
def Frame.weight : Frame d → Nat
  | .str _ => 1
  | .ops _ os => opsWeight os + 1
  | .blocks _ bs => blocksWeight bs + 1
  | .regions _ rs => regionsWeight rs + 1
  | .items is => itemsWeight is + 1

/-- A measure of a stack of frames. -/
def framesWeight : List (Frame d) → Nat
  | [] => 0
  | f :: fs => f.weight + framesWeight fs

theorem opWeight_eq (o : Operation d) : opWeight o = regionsWeight o.regions + 1 := by
  cases o; simp [opWeight]

theorem blocksWeight_cons (b : Block d) (bs : List (Block d)) :
    blocksWeight (b :: bs) = opsWeight b.body + blocksWeight bs + 3 := by
  cases b; simp [blocksWeight]

theorem regionsWeight_cons (r : Region d) (rs : List (Region d)) :
    regionsWeight (r :: rs) = blocksWeight r.blocks + regionsWeight rs + 3 := by
  cases r; simp [regionsWeight]

variable [DialectText d]

/-- `printDef`, compiled after `print_eq_printAttr`. -/
def defText (x : Name × d.Ty) : String := "%" ++ x.1 ++ ": " ++ (tyAttr x.2).print

/-- `printDefs`, compiled after `print_eq_printAttr`. -/
def defsText (xs : List (Name × d.Ty)) : String := ", ".intercalate (xs.map defText)

theorem defsText_eq : @defsText = @printDefs := rfl

/-- The text of an op before its regions: its indentation, its results, its
name, its attributes, its operands and its successors. -/
def opHead (n : Nat) (o : Operation d) : String :=
  let lhs := if o.results.isEmpty then "" else defsText o.results ++ " = "
  let head := " ".intercalate (opName o.op :: (opAttrs o.op).map Attr.print)
  let uses := o.operands.map ("%" ++ ·) ++ o.succs.map Succ.print
  let rhs := if uses.isEmpty then head else head ++ " " ++ ", ".intercalate uses
  indent n ++ lhs ++ rhs

/-- The line of a block's label. -/
def blockHead (n : Nat) (b : Block d) : String :=
  indent n ++ "^" ++ b.label ++
    (if b.params.isEmpty then "" else "(" ++ defsText b.params ++ ")") ++ ":\n"

/-- The line of a function's header, through its `{`. -/
def funcHead (f : Func d) : String :=
  let results :=
    if f.results.isEmpty then "" else " -> " ++ ", ".intercalate (f.results.map (tyAttr · |>.print))
  "func " ++ printSymbol f.name ++ "(" ++ defsText f.params ++ ")" ++ results ++ " {\n"

/-- The text that a frame stands for, by the spec's printer. -/
def Frame.text : Frame d → String
  | .str s => s
  | .ops n os => Operation.printList n os
  | .blocks n bs => Block.printList n bs
  | .regions n rs => Region.printList n rs
  | .items is => String.join (is.map (·.print ++ "\n"))

/-- Appends the text of each frame to `acc`, the top of the stack first.
Every call is a tail call, so the loop takes no stack. -/
def printFrames (acc : String) : List (Frame d) → String
  | [] => acc
  | .str s :: fs => printFrames (acc ++ s) fs
  | .ops _ [] :: fs => printFrames acc fs
  | .ops n (o :: os) :: fs =>
    printFrames (acc ++ opHead n o)
      (.regions n o.regions :: .str (" " ++ printLocRef o.loc ++ "\n") :: .ops n os :: fs)
  | .blocks _ [] :: fs => printFrames acc fs
  | .blocks n (b :: bs) :: fs =>
    printFrames (acc ++ blockHead n b) (.ops (n + 2) b.body :: .blocks n bs :: fs)
  | .regions _ [] :: fs => printFrames acc fs
  | .regions n (r :: rs) :: fs =>
    printFrames (acc ++ " {\n")
      (.blocks (n + 2) r.blocks :: .str (indent n ++ "}") :: .regions n rs :: fs)
  | .items [] :: fs => printFrames acc fs
  | .items (.func f :: is) :: fs =>
    printFrames (acc ++ funcHead f)
      (.blocks 0 f.body.blocks :: .str "}\n" :: .str "\n" :: .items is :: fs)
termination_by fs => framesWeight fs
decreasing_by
  all_goals
    simp only [framesWeight, Frame.weight, opsWeight, opWeight_eq, blocksWeight_cons,
      regionsWeight_cons, itemsWeight]
    omega

/-- A module in text: `Module.print`, with no stack per level of regions
and in linear time. -/
def printModule (m : Module d) : String := printFrames "" [.items m.items, .str m.locs.print]

/-- The loop appends the text of its frames. -/
theorem printFrames_eq (acc : String) (fs : List (Frame d)) :
    printFrames acc fs = acc ++ String.join (fs.map Frame.text) := by
  fun_induction printFrames acc fs with
  | case1 acc => simp
  | case4 acc n o os fs ih =>
    rw [ih]
    cases o
    simp only [Frame.text, Operation.printList, Operation.print, opHead, defsText_eq,
      List.map_cons, String.join_cons, String.append_assoc]
  | case6 acc n b bs fs ih =>
    rw [ih]
    cases b
    simp only [Frame.text, Block.printList, blockHead, defsText_eq, List.map_cons,
      String.join_cons, String.append_assoc]
  | case8 acc n r rs fs ih =>
    rw [ih]
    cases r
    simp only [Frame.text, Region.printList, List.map_cons, String.join_cons, String.append_assoc]
  | case10 acc f is fs ih =>
    rw [ih]
    simp only [Frame.text, Item.print, Func.print, funcHead, defsText_eq, List.map_cons,
      String.join_cons, String.append_assoc]
  | _ => rename_i ih; rw [ih]; simp [Frame.text, Operation.printList, Block.printList,
      Region.printList, String.append_assoc]

/-- `printModule` prints as the spec's printer does, so `fir-ref` runs it in
place of `Module.print`. -/
@[csimp] theorem print_eq_printModule : @Module.print = @printModule := by
  funext d _ m
  simp [printModule, printFrames_eq, Frame.text, Module.print]

end FirRef
