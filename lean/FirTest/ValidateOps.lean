import FirTest.Parse

/-!
Tests of the validation check (`Module.problems`) on the rules of ops, and
on the core dialect's own rules: for each rule, a module that breaks it and
one that keeps it. A module that the parser can read is written as text; one
that no text can hold, such as an op whose operand types are not those of
its op instance, is built in Lean. Each check compares the messages of the
problems, so it also checks that the check names the right op.
-/

namespace FirTest

open Fir Fir.Core

/-- The messages of the problems of a module. -/
def messages (m : Module CoreDialect) : List String := m.problems.map (·.message)

/-- The text parses, and the check finds exactly the problems `ms`. -/
def checks (t : String) (ms : List String) : Bool :=
  match parseCore t with
  | .ok m => messages m == ms
  | .error _ => false

/-- The text parses, and the module is valid. -/
def valid (t : String) : Bool := checks t []

/-- A module of one function whose entry block holds `ops`, with the
location table `@0 = unknown`. -/
def entryOnly (ops : List (Operation CoreDialect)) (params : List (Name × Ty) := [])
    (results : List Ty := []) : Module CoreDialect :=
  ⟨[.func ⟨"f", params, results, ⟨[⟨"e", [], ops⟩]⟩⟩], [(0, .unknown)]⟩

/-! # Every op of the core dialect, in a valid function -/

/-- A function that uses each of the 24 core ops validly. -/
def everyOp : String := oneFunc ("func @all(%a: i32, %b: i32, %c: i1) -> i32 {\n^entry:\n" ++
  String.join (["%k: i32 = const 7", "%s1: i32 = add nuw nsw %a, %b", "%s2: i32 = sub %a, %b",
    "%s3: i32 = mul %a, %k", "%s4: i32 = sdiv exact %a, %b", "%s5: i32 = udiv %a, %b",
    "%s6: i32 = srem %a, %b", "%s7: i32 = urem %a, %b", "%s8: i32 = and %a, %b",
    "%s9: i32 = or %a, %b", "%s10: i32 = xor %a, %b", "%s11: i32 = shl %a, %b",
    "%s12: i32 = lshr %a, %b", "%s13: i32 = ashr %a, %b", "%lt: i1 = icmp slt %a, %b",
    "%sel: i32 = select %lt, %a, %b", "%w: i64 = zext %a", "%v: i64 = sext %a",
    "%t: i8 = trunc %a", "%f: i32 = freeze %sel", "%r: i32 = call @all %a, %b, %c",
    "cond_br %c, ^x(%f), ^y"].map ("  " ++ · ++ " @0\n")) ++
  "^x(%p: i32):\n  br ^y @0\n^y:\n  ret %a @0\n}\n")

#guard valid everyOp

/-! # An op owns no region -/

#guard checks (func ["br {\n  ^inner:\n    ret @0\n  } @0"])
  ["the op owns a region: no op may own one yet",
   "the op has 0 successors, and its op instance has 1"]

/-! # Operand and result types -/

#guard messages (entryOnly [op [("x", .int 32)] (.add 32 {}) ["a", "a"], op [] (.ret []) []]
    [("a", .int 8)]) ==
  ["an operand of the op is not of the type that its op instance takes"]
#guard messages (entryOnly [op [("x", .int 8)] (.add 8 {}) ["a"], op [] (.ret []) []]
    [("a", .int 8)]) ==
  ["the op has 1 operands, and its op instance takes 2"]
#guard messages (entryOnly [op [("x", .int 8)] (.add 8 {}) ["a", "b"], op [] (.ret []) []]
    [("a", .int 8)]) ==
  ["an operand of the op is not of the type that its op instance takes",
   "%b is not defined in the function"]
#guard messages (entryOnly [op [("x", .int 8)] (.const 32 0) [], op [] (.ret []) []]) ==
  ["a result of the op is not of the type that its op instance gives"]
#guard messages (entryOnly [op [] (.const 32 0) [], op [] (.ret []) []]) ==
  ["the op has 0 results, and its op instance gives 1"]
#guard messages (entryOnly [op [("x", .int 8)] (.add 8 {}) ["a", "a"], op [] (.ret []) []]
  [("a", .int 8)]) == []

/-! # Terminators end blocks, and only they have successors -/

#guard checks (func ["ret %a @0", "%c: i32 = const 1 @0"])
  ["the op ends a block, and is not the last op of ^entry",
   "block ^entry does not end with a terminator"]
#guard messages (entryOnly [op [] .br []]) == ["the op has 0 successors, and its op instance has 1"]
#guard messages (entryOnly [op [("c", .int 8)] (.const 8 0) [] 0 [⟨"e", []⟩], op [] (.ret []) []])
  == ["the op has 1 successors, and its op instance has 0",
      "the op is not a terminator, and only terminators have successors",
      "no branch may go to the entry block ^e"]

/-! # Successors -/

/-- A function `@f(%a: i32, %c: i1)` whose entry block ends with `term`,
followed by the blocks `rest`. -/
def branches (term : String) (rest : String) : String :=
  oneFunc ("func @f(%a: i32, %c: i1) {\n^entry:\n  " ++ term ++ " @0\n" ++ rest ++ "}\n")

#guard checks (branches "br ^entry" "") ["no branch may go to the entry block ^entry"]
#guard checks (branches "br ^nowhere" "") ["successor ^nowhere is not a block of the function"]
#guard checks (branches "br ^b(%c)" "^b(%x: i32):\n  ret @0\n")
  ["successor ^b does not pass one value of the right type for each argument of the block"]
#guard checks (branches "br ^b" "^b(%x: i32):\n  ret @0\n")
  ["successor ^b does not pass one value of the right type for each argument of the block"]
#guard valid (branches "br ^b(%a)" "^b(%x: i32):\n  ret @0\n")

/-! # Uses are in scope -/

#guard checks (branches "br ^b(%nope)" "^b(%x: i32):\n  ret @0\n")
  ["successor ^b does not pass one value of the right type for each argument of the block",
   "%nope is not defined in the function"]
#guard checks (branches "cond_br %c, ^x, ^y" "^x:\n  %v: i32 = const 1 @0\n  br ^y @0\n^y:\n  %w: i32 = add %v, %a @0\n  ret @0\n")
  ["%v is defined in ^x, which does not dominate ^y"]
#guard checks (branches "cond_br %c, ^x(%a), ^y" "^x(%p: i32):\n  br ^y @0\n^y:\n  %w: i32 = add %p, %a @0\n  ret @0\n")
  ["%p is an argument of ^x, which does not dominate ^y"]
#guard valid (branches "br ^x(%a)" "^x(%p: i32):\n  %v: i32 = const 1 @0\n  br ^y @0\n^y:\n  %w: i32 = add %p, %v @0\n  ret @0\n")
#guard checks (func ["%b: i32 = add %c, %a @0", "%c: i32 = const 1 @0", "ret %b @0"])
  ["%c is used before it is defined"]
#guard checks (func ["br {\n  ^r:\n    %x: i32 = const 1 @0\n    ret @0\n  } @0", "ret %x @0"])
  ["the op owns a region: no op may own one yet",
   "the op ends a block, and is not the last op of ^entry",
   "the op has 0 successors, and its op instance has 1",
   "%x is defined inside a region, and is not in scope here"]

/-! # Symbols, the dialect's own rule and locations -/

/-- A text with the function `@g(%x: i8) -> i8` and the function `f`. -/
def withG (f : String) : String :=
  oneFunc ("func @g(%x: i8) -> i8 {\n^e:\n  ret %x @0\n}\n\n" ++ f)

#guard valid (withG "func @f(%a: i8) -> i8 {\n^e:\n  %r: i8 = call @g %a @0\n  ret %r @0\n}\n")
#guard checks (withG "func @f(%a: i8) -> i8 {\n^e:\n  %r: i8 = call @h %a @0\n  ret %r @0\n}\n")
  ["the op refers to @h, which names no function", "the op breaks its dialect's own rule"]
#guard checks (withG "func @f(%a: i16) -> i8 {\n^e:\n  %r: i8 = call @g %a @0\n  ret %r @0\n}\n")
  ["the op breaks its dialect's own rule"]
#guard valid (func ["%b: i64 = zext %a @0", "ret %a @0"])
#guard checks (func ["ret @0"]) ["the op breaks its dialect's own rule"]
#guard valid (func ["%b: i64 = sext %a @0", "ret %a @0"])
#guard ["zext", "sext"].all fun w =>
  checks (func [s!"%b: i32 = {w} %a @0", "ret %a @0"]) ["the op breaks its dialect's own rule"] &&
  checks (func [s!"%b: i8 = {w} %a @0", "ret %a @0"]) ["the op breaks its dialect's own rule"]
#guard valid (func ["%b: i8 = trunc %a @0", "ret %a @0"])
#guard checks (func ["%b: i32 = trunc %a @0", "ret %a @0"]) ["the op breaks its dialect's own rule"]
#guard checks (func ["%b: i64 = trunc %a @0", "ret %a @0"]) ["the op breaks its dialect's own rule"]
#guard checks (func ["ret %a @1"]) ["location reference @1 is not in the location table"]

/-! # Core types -/

#guard checks (oneFunc "func @f(%a: i0, %p: ptr) -> i0 {\n^e:\n  ret @0\n}\n")
  ["a result type of the function is not valid", "the type of %a is not valid",
   "the type of %p is not valid", "the op breaks its dialect's own rule"]
#guard valid (oneFunc "func @f(%a: i1, %b: i16777215) {\n^e:\n  ret @0\n}\n")
#guard messages (entryOnly [op [] (.ret []) []] [("a", .int (maxWidth + 1))]) ==
  ["the type of %a is not valid"]

end FirTest
