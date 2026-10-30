import Fir.Text.Print

/-!
`fir-ref` prints attributes with `printAttr`, not with the spec's
`Attr.print`, which recurses once per level of nesting and copies the
arguments' text at each level. `printAttr` keeps what is left to print on
an explicit stack of frames and appends each piece of text to one
accumulator, so it takes no stack per level and runs in time linear in the
text it writes. The theorem `print_eq_printAttr` proves the two equal, and
`@[csimp]` makes Lean compile every later call of `Attr.print` as a call of
`printAttr` (ADR-2026-10-30-1450).
-/

namespace FirRef

open Fir Fir.Text

/-- What is left to print of an attribute. -/
inductive AttrFrame where
  /-- A whole attribute. -/
  | attr (a : Attr)
  /-- The arguments of an applied attribute after its first, each after a
  comma and a space, then the closing parenthesis. -/
  | args (as : List Attr)

/-- The text that a frame stands for, by the spec's printer. -/
def AttrFrame.text : AttrFrame → String
  | .attr a => a.print
  | .args as => String.join (as.map (", " ++ ·.print)) ++ ")"

mutual
/-- A measure of an attribute that each step of `printAttrs` lowers. -/
def attrWeight : Attr → Nat
  | .app _ args => argsWeight args + 1
  | _ => 1

/-- A measure of attributes that each step of `printAttrs` lowers. -/
def argsWeight : List Attr → Nat
  | [] => 0
  | a :: as => attrWeight a + argsWeight as + 3
end

/-- A measure of a frame. -/
def AttrFrame.weight : AttrFrame → Nat
  | .attr a => attrWeight a
  | .args as => argsWeight as + 1

/-- A measure of a stack of frames. -/
def attrFramesWeight : List AttrFrame → Nat
  | [] => 0
  | f :: fs => f.weight + attrFramesWeight fs

/-- Appends the text of each frame to `acc`, the top of the stack first.
Every call is a tail call, so the loop takes no stack. -/
def printAttrs (acc : String) : List AttrFrame → String
  | [] => acc
  | .attr (.word w) :: fs => printAttrs (acc ++ w) fs
  | .attr (.int i) :: fs => printAttrs (acc ++ printInt i) fs
  | .attr (.str s) :: fs => printAttrs (acc ++ quote s) fs
  | .attr (.sym s) :: fs => printAttrs (acc ++ printSymbol s) fs
  | .attr (.app h []) :: fs => printAttrs (acc ++ h ++ "(" ++ ")") fs
  | .attr (.app h (a :: as)) :: fs => printAttrs (acc ++ h ++ "(") (.attr a :: .args as :: fs)
  | .args [] :: fs => printAttrs (acc ++ ")") fs
  | .args (a :: as) :: fs => printAttrs (acc ++ ", ") (.attr a :: .args as :: fs)
termination_by fs => attrFramesWeight fs
decreasing_by
  all_goals simp only [attrFramesWeight, AttrFrame.weight, attrWeight, argsWeight]; omega

/-- An attribute, or a type, in text: `Attr.print`, with no stack per level
and in linear time. -/
def printAttr (a : Attr) : String := printAttrs "" [.attr a]

/-- The arguments of an applied attribute after the first: the spec's
separators, written as a prefix of each argument. -/
theorem intercalate_printList (a : Attr) (as : List Attr) :
    ", ".intercalate (Attr.print.printList (a :: as)) =
      a.print ++ String.join (as.map (", " ++ ·.print)) := by
  induction as generalizing a with
  | nil => simp [Attr.print.printList]
  | cons b bs ih =>
    rw [Attr.print.printList, Attr.print.printList, String.intercalate_cons_cons,
      ← Attr.print.printList, ih]
    simp [String.append_assoc]

/-- The loop appends the text of its frames. -/
theorem printAttrs_eq (acc : String) (fs : List AttrFrame) :
    printAttrs acc fs = acc ++ String.join (fs.map AttrFrame.text) := by
  fun_induction printAttrs acc fs with
  | case1 acc => simp
  | case6 acc h fs ih =>
    rw [ih]
    simp [AttrFrame.text, Attr.print, Attr.print.printList, String.append_assoc]
  | case7 acc h a as fs ih =>
    rw [ih]
    simp only [AttrFrame.text, Attr.print, intercalate_printList, List.map_cons, String.join_cons,
      String.append_assoc]
  | case9 acc a as fs ih =>
    rw [ih]
    simp [AttrFrame.text, String.append_assoc]
  | _ => rename_i ih; rw [ih]; simp [AttrFrame.text, Attr.print, String.append_assoc]

/-- `printAttr` prints as the spec's printer does, so `fir-ref` runs it in
place of `Attr.print`. -/
@[csimp] theorem print_eq_printAttr : @Attr.print = @printAttr := by
  funext a
  simp [printAttr, printAttrs_eq, AttrFrame.text]

end FirRef
