import Fir.Text.Grammar

/-!
Every dialect other than the core writes its ops, types and attributes as
`name.word`, where `name` is the dialect's name, and the core writes bare
words (ADR-2026-11-09-1543). So a word says which dialect it belongs to: the
part before its first `.`, or the core when it has none. `gpu.launch`
belongs to the dialect `gpu`, `toy.a.b` to `toy`, and `add` to the core.
A module that holds several dialects reads each word with the dialect that
the word names.

A type, and an attribute that is not a number, a string or a symbol, is a
word or a word applied to attributes. A type belongs to the dialect of its
head word, so `toy.vec(4, i32)` is a type of `toy`, and its argument `i32`
is the core's. Every word of an attribute names a dialect, or none.

A dialect has a _dialect set_: the names of the dialects that its words may
name. The core's words are bare, so the core's set is empty. A dialect's
words name only dialects of its set: each op name, each word of an op's
attributes and each word of a valid type. The section on sums of dialects
builds a dialect from several, and its set holds the name of each of them.

This section gives, in order: the dialect that a word names, the dialects
that an attribute names, a dialect's name and its dialect set, and the law
that a dialect's words name only dialects of its set.
-/

namespace Fir

/-!
# The dialect of a word
-/

/-- The dialect that the word `w` names: the part of `w` before its first
`.`, or `none` when `w` holds no `.` and is the core's. -/
def wordDialect (w : String) : Option String :=
  if '.' ∈ w.toList then some (String.ofList (w.toList.takeWhile (· ≠ '.'))) else none

#guard wordDialect "gpu.launch" == some "gpu" && wordDialect "toy.a.b" == some "toy"
#guard wordDialect "plain" == none && wordDialect ".x" == some ""

/-- A word `n.w`, where `n` holds no `.`, names the dialect `n`. -/
theorem wordDialect_dot {n : String} (hn : '.' ∉ n.toList) (w : String) :
    wordDialect (n ++ "." ++ w) = some n := by
  have hpre : ∀ (l r : List Char), '.' ∉ l →
      (l ++ '.' :: r).takeWhile (fun c => decide (c ≠ '.')) = l := by
    intro l r h
    induction l with
    | nil => exact List.takeWhile_cons_of_neg (by simp)
    | cons c l ih =>
      have hc : c ≠ '.' := fun e => h (e ▸ List.mem_cons_self)
      rw [List.cons_append, List.takeWhile_cons_of_pos (by simpa using hc),
        ih (fun m => h (List.mem_cons_of_mem _ m))]
  have hdot : '.' ∈ (n ++ "." ++ w).toList := by simp [String.toList_append]
  rw [wordDialect, ite_eq_left hdot]
  simp only [String.toList_append]
  rw [show n.toList ++ ".".toList ++ w.toList = n.toList ++ '.' :: w.toList by simp,
    hpre _ _ hn, String.ofList_toList]

/-!
# The dialects of an attribute
-/

/-- The head word of a type or an attribute: the word itself, or the word
that an applied attribute applies. A number, a string and a symbol have
none. -/
def Attr.head? : Attr → Option String
  | .word w | .app w _ => some w
  | _ => none

/-- The dialect that a type belongs to: the dialect that its head word
names. -/
def Attr.dialect? (a : Attr) : Option String := a.head?.bind wordDialect

mutual
/-- The dialects that the words of an attribute name, in order, at any
depth: a word names one dialect or none, and an applied attribute the
dialects of its head and of its arguments. -/
def Attr.dialects : Attr → List String
  | .word w => (wordDialect w).toList
  | .app h args => (wordDialect h).toList ++ Attr.dialectsAll args
  | .int _ | .str _ | .sym _ => []

/-- The dialects that the words of a list of attributes name. -/
def Attr.dialectsAll : List Attr → List String
  | [] => []
  | a :: as => a.dialects ++ Attr.dialectsAll as
end

/-- The dialect of a type is one of the dialects that its words name. -/
theorem Attr.dialect?_mem {a : Attr} {x : String} (h : a.dialect? = some x) :
    x ∈ a.dialects := by
  cases a <;> simp_all [Attr.dialect?, Attr.head?, Attr.dialects]

/-- The dialects that a list of attributes names are those that its
attributes name. -/
theorem Attr.mem_dialectsAll {as : List Attr} {x : String} :
    x ∈ Attr.dialectsAll as ↔ ∃ a ∈ as, x ∈ a.dialects := by
  induction as with
  | nil => simp [Attr.dialectsAll]
  | cons a as ih => simp [Attr.dialectsAll, ih]

/-!
# Names and dialect sets
-/

/-- The name of a dialect other than the core: the word before the `.` of
each of its own words. It holds no `.`, or no word would name it. -/
class DialectName (d : Dialect) where
  name : String
export DialectName (name)

/-- The dialect set of a dialect: the names of the dialects that its words
may name. A bare word is the core's, and every dialect may write one. -/
class DialectSet (d : Dialect) where
  names : List String
export DialectSet (names)

/-- The words of a dialect name only dialects of its set: each op name, each
word of an op's attributes and each word of a valid type. -/
class LawfulDialectSet (d : Dialect) [DialectValidation d] [DialectText d] [DialectSet d] :
    Prop where
  opName_mem : ∀ (op : d.Op) (x : String), wordDialect (opName op) = some x → x ∈ names d
  opAttrs_mem : ∀ (op : d.Op), ∀ x ∈ Attr.dialectsAll (opAttrs op), x ∈ names d
  tyAttr_mem : ∀ t : d.Ty, validTy t → ∀ x ∈ (tyAttr t).dialects, x ∈ names d

end Fir
