import FirTest.Print
import FirTest.ValidateOps
import FirRef.Report

/-!
Tests of the validation check (`Module.problems`) on the rules of modules,
location tables and functions, of the reports of `fir-ref validate`
(`FirRef.validateBytes`), and of the check at any depth of nesting. Through
`FirRef.Report`, this module imports `FirRef.Fast`, as `fir-ref` does, so
the checks below run `FirRef.moduleProblems`, which walks nested blocks with
`FirRef.allBlocks`. The check on regions nested 1,000,000 levels deep needs
it: the spec's `Func.allBlocks` overflows the stack there. The last checks
pin the axioms of the theorems to Lean's standard ones.
-/

namespace FirTest

open Fir Fir.Core

/-- A module of the functions `fs` with the location table `locs`. -/
def moduleOf (fs : List (Func CoreDialect)) (locs : LocTable := [(0, .unknown)]) :
    Module CoreDialect :=
  ⟨fs.map .func, locs⟩

/-- A function `@name` whose one block returns nothing. -/
def empty (name : Name) : Func CoreDialect := ⟨name, [], [], ⟨[⟨"e", [], [op [] (.ret []) []]⟩]⟩⟩

/-- A function with the blocks `bs`. -/
def withBlocks (bs : List (Block CoreDialect)) (params : List (Name × Ty) := []) :
    Func CoreDialect :=
  ⟨"f", params, [], ⟨bs⟩⟩

/-- A block labelled `l` that returns nothing. -/
def retBlock (l : Name) (params : List (Name × Ty) := []) : Block CoreDialect :=
  ⟨l, params, [op [] (.ret []) []]⟩

/-! # The shared corpus, and every verdict -/

#guard [Example.sumModule.print, seven, everyOp].all valid
#guard checks (oneFunc "func @f() {\n^e:\n  ret @0\n}\n\nfunc @f() {\n^e:\n  ret @0\n}\n")
  ["the symbol @f names more than one item"]
#guard Rejects.deadModule.problems.map (·.block) == [some "dead"]

/-- The report on a text, and the exit status. -/
def report (t : String) : String × UInt32 := FirRef.validateBytes "t.fir" t.toUTF8

#guard report seven == ("{\"file\":\"t.fir\",\"verdict\":\"accepted\",\"diagnostics\":[]}", 0)
#guard report Rejects.deadModule.print ==
  ("{\"file\":\"t.fir\",\"verdict\":\"validation-error\",\"diagnostics\":[{\"kind\":" ++
    "\"validation-error\",\"message\":\"block ^dead is not reachable from the entry\"," ++
    "\"func\":\"f\",\"block\":\"dead\",\"op\":null,\"loc\":{\"ref\":0,\"location\":" ++
    "\"unknown\"}}]}", 1)
#guard report (func ["ret %a @7"]) ==
  ("{\"file\":\"t.fir\",\"verdict\":\"validation-error\",\"diagnostics\":[{\"kind\":" ++
    "\"validation-error\",\"message\":\"location reference @7 is not in the location " ++
    "table\",\"func\":\"f\",\"block\":\"entry\",\"op\":0,\"loc\":{\"ref\":7,\"location\":" ++
    "null}}]}", 1)
#guard report "func @f() {\n" ==
  ("{\"file\":\"t.fir\",\"verdict\":\"parse-error\",\"diagnostics\":[{\"kind\":" ++
    "\"parse-error\",\"message\":\"expected } to close the item's body, found the end of " ++
    "the text\"," ++
    "\"line\":2,\"column\":1}]}", 1)
#guard (FirRef.validateBytes "t.fir" ⟨#[0x6c, 0x0a, 0xff]⟩).1.endsWith
  "\"line\":2,\"column\":1}]}"
#guard FirRef.ioErrorReport "-" "cannot read standard input: closed" ==
  "{\"file\":\"-\",\"verdict\":\"io-error\",\"diagnostics\":[{\"kind\":\"io-error\"," ++
    "\"message\":\"cannot read standard input: closed\"}]}"
#guard FirRef.jsonString ("a\"b\\c\n\x01\u2028é\u0085\u202e" ++ (Char.ofNat 0xe007f).toString) ==
  "\"a\\\"b\\\\c\\n\\u0001\\u2028é\\u0085\\u202e\\udb40\\udc7f\""

/-! # Symbols and the location table -/

#guard messages (moduleOf [empty "f", empty "g"]) == []
#guard messages (moduleOf [empty "\u202e", empty "\u202e"]) ==
  ["the symbol @\"\\u{202e}\" names more than one item"]
#guard messages (moduleOf [] [(0, .unknown), (1, .derived 0), (2, .callsite 0 1),
  (3, .fused [0, 2]), (4, .range "f" 1 0 1 0), (5, .range "f" 2 9 3 1), (6, .range "f" 7 3 7 3),
  (7, .range "f" 4294967295 4294967295 4294967295 4294967295), (4294967295, .name "n")]) == []
#guard messages (moduleOf [] [(1, .unknown), (0, .unknown), (0, .unknown)]) ==
  ["location table: @0 comes after @1: references are unique and in increasing order",
   "location table: @0 comes after @0: references are unique and in increasing order"]
#guard messages (moduleOf [] [(4294967296, .unknown), (0, .range "f" 1 1 1 4294967296)]) ==
  ["location table: @0 comes after @4294967296: references are unique and in increasing order",
   "location table: @4294967296 holds a reference, line or column of 2^32 or more",
   "location table: @0 holds a reference, line or column of 2^32 or more"]
#guard messages (moduleOf [] [(0, .range "f" 0 1 1 1), (1, .range "f" 2 1 1 1),
    (2, .range "f" 1 5 1 3), (3, .fused [0])]) ==
  ["location table: @0 is not well formed: a range starts at line 1 or later",
   "location table: @1 is not well formed: a range does not end before it starts",
   "location table: @2 is not well formed: a range does not end before it starts",
   "location table: @3 is not well formed: a fused location fuses at least two"]
#guard messages (moduleOf [] [(0, .derived 0), (1, .callsite 0 5)]) ==
  ["location table: @0 refers to @0, which does not come before it",
   "location table: @1 refers to @5, which the table does not hold"]

/-! # Functions -/

#guard messages (moduleOf [withBlocks []]) == ["the function has no entry block"]
#guard messages (moduleOf [withBlocks [retBlock "e" [("x", .int 8)]]]) ==
  ["the entry block ^e declares arguments: its arguments are the function's parameters"]
#guard checks (oneFunc "func @f() {\n^e:\n  ret @0\n^e:\n  ret @0\n}\n")
  ["label ^e names more than one block"]
#guard messages (moduleOf [withBlocks [retBlock "e", retBlock "e"]]) ==
  ["label ^e names more than one block"]
#guard (moduleOf [withBlocks [⟨"e", [], [op [] (.ret []) [] 3]⟩,
    ⟨"e", [], [op [] (.ret []) [] 5]⟩]] [(3, .unknown), (5, .unknown)]).problems.map (·.loc)
  == [some 3]
#guard messages (moduleOf [withBlocks [retBlock "e", retBlock "b"]]) ==
  ["block ^b is not reachable from the entry"]
#guard messages (moduleOf [withBlocks [⟨"e", [], [op [] .br [] 0 [⟨"b", []⟩]]⟩, retBlock "b"]])
  == []
#guard messages (moduleOf [withBlocks [⟨"e", [], [op [("x", .int 8)] (.const 8 0) [],
    op [("x", .int 8)] (.const 8 1) [], op [] (.ret []) []]⟩] [("x", .int 8)]]) ==
  ["value %x is defined more than once", "value %x is defined more than once"]
#guard messages (moduleOf [withBlocks [retBlock "e"] [("a b", .int 8), ("", .int 8)]]) ==
  ["value name \"a b\" is not one or more name characters",
   "value name \"\" is not one or more name characters"]
#guard messages (moduleOf [withBlocks [⟨"e", [], [op [] .br [] 0 [⟨"b c", []⟩]]⟩,
    retBlock "b c"]]) ==
  ["label \"b c\" is not one or more name characters"]
#guard messages (moduleOf [withBlocks [⟨"e", [], [op [] .br [] 0 [⟨"b", []⟩]]⟩, ⟨"b", [], []⟩]])
  == ["block ^b holds no ops"]

/-! # At any depth -/

/-- A function whose entry block holds an op that owns a region, whose one
block holds an op that owns a region, and so on, `n` levels deep; the
innermost block holds `inner`. -/
def deep (n : Nat) (inner : List (Operation CoreDialect)) : Module CoreDialect :=
  let body := Nat.repeat (fun os => [⟨[], .br, [], [⟨"b", []⟩], [⟨[⟨"b", [], os⟩]⟩], 0⟩]) n inner
  moduleOf [⟨"f", [], [], ⟨[⟨"e", [], body⟩, retBlock "b"]⟩⟩]

/-- What the check finds in `deep n` whose innermost op defines a value of
type `i0`: the region of the top op, and the type, `n` levels down. -/
def deepProblems : List String :=
  ["the type of %x is not valid", "the op owns a region: no op may own one yet"]

#guard messages (deep 3 [op [] (.ret []) []]) == ["the op owns a region: no op may own one yet"]
#guard messages (deep 3 [op [("x", .int 0)] (.const 0 0) []]) == deepProblems
#guard messages (deep 1000000 [op [("x", .int 0)] (.const 0 0) []]) == deepProblems
#guard messages (deep 1000000 [op [("y", .int 8)] (.const 8 0) [], op [("y", .int 8)] (.const 8 1) []])
  == ["value %y is defined more than once", "the op owns a region: no op may own one yet"]
#guard messages (nested 1000) ==
  ["the op owns a region: no op may own one yet",
   "the op has 0 successors, and its op instance has 1"]

/-! # The axioms of the proofs -/

/--
info: 'Fir.Module.problems_eq_nil_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fir.Module.problems_eq_nil_iff

/--
info: 'FirRef.allBlocks_eq_allBlocks' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms FirRef.allBlocks_eq_allBlocks

/--
info: 'Fir.Core.Rejects.deadBlock_problems' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fir.Core.Rejects.deadBlock_problems

end FirTest
