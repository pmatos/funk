import Fir.Validation.CheckModule
import Fir.Sum.Names
import FirRef.PrintAttr

/-!
`fir-ref` walks the attributes of an item of a dialect's kind with loops,
not with the spec's `Attr.allWritable` and `Attr.dialectsAll`, which recurse
once per level of an applied attribute. Every reader decodes such an item
whatever its dialect, and keeps its attributes as the text writes them, so
a text can nest them to any depth (ADR-2026-11-10-2224). `writableLoop` and
`dialectsLoop` keep what is left to walk on a stack of attributes, so they
take no stack per level (the depth rule, ADR-2026-11-09-1941). The theorems
below prove each equal to the spec's function, and `@[csimp]` makes Lean
compile every later call of the spec's as a call of the loop.
-/

namespace FirRef

open Fir

/-- The measure of attributes adds up over a list. -/
theorem argsWeight_append : ∀ as bs : List Attr, argsWeight (as ++ bs) = argsWeight as + argsWeight bs
  | [], _ => by simp [argsWeight]
  | a :: as, bs => by simp [argsWeight, argsWeight_append as bs]; omega

/-- `Attr.allWritable`, with the attributes left to check on a stack. Every
call to itself is a tail call. -/
def writableLoop : List Attr → Bool
  | [] => true
  | .word w :: st => if isWord w then writableLoop st else false
  | .app h args :: st => if isWord h then writableLoop (args ++ st) else false
  | .int _ :: st | .str _ :: st | .sym _ :: st => writableLoop st
termination_by st => argsWeight st
decreasing_by all_goals simp only [argsWeight, attrWeight, argsWeight_append]; omega

theorem allWritable_append : ∀ as bs : List Attr,
    Attr.allWritable (as ++ bs) = (Attr.allWritable as && Attr.allWritable bs)
  | [], _ => by simp [Attr.allWritable]
  | a :: as, bs => by
    simp only [List.cons_append, Attr.allWritable, allWritable_append as bs, Bool.and_assoc]

theorem writableLoop_eq (st : List Attr) : writableLoop st = Attr.allWritable st := by
  fun_induction writableLoop st <;>
    simp_all [Attr.allWritable, Attr.writable, allWritable_append]

@[csimp] theorem allWritable_eq_writableLoop : @Attr.allWritable = @writableLoop :=
  funext fun st => (writableLoop_eq st).symm

/-- `Attr.dialectsAll`, with the attributes left to walk on a stack and the
dialects found so far in `acc`, last first. Every call to itself is a tail
call. -/
def dialectsLoop (acc : List String) : List Attr → List String
  | [] => acc.reverse
  | .word w :: st => dialectsLoop ((wordDialect w).toList.reverse ++ acc) st
  | .app h args :: st => dialectsLoop ((wordDialect h).toList.reverse ++ acc) (args ++ st)
  | .int _ :: st | .str _ :: st | .sym _ :: st => dialectsLoop acc st
termination_by st => argsWeight st
decreasing_by all_goals simp only [argsWeight, attrWeight, argsWeight_append]; omega

theorem dialectsAll_append : ∀ as bs : List Attr,
    Attr.dialectsAll (as ++ bs) = Attr.dialectsAll as ++ Attr.dialectsAll bs
  | [], _ => by simp [Attr.dialectsAll]
  | a :: as, bs => by simp [Attr.dialectsAll, dialectsAll_append as bs]

theorem dialectsLoop_eq (acc : List String) (st : List Attr) :
    dialectsLoop acc st = acc.reverse ++ Attr.dialectsAll st := by
  fun_induction dialectsLoop acc st <;>
    simp_all [Attr.dialectsAll, Attr.dialects, dialectsAll_append]

/-- The dialects that attributes name, by `dialectsLoop`. -/
def dialectsOf (as : List Attr) : List String := dialectsLoop [] as

@[csimp] theorem dialectsAll_eq_dialectsOf : @Attr.dialectsAll = @dialectsOf :=
  funext fun st => by simp [dialectsOf, dialectsLoop_eq]

end FirRef
