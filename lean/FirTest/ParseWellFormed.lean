import FirTest.Parse
import FirTest.Mixed

/-!
Tests of #105's theorem, `parse_wellFormed`: every module that the parser
gives is well formed, so its printed form reads back as it
(`parse_print_of_parse`), and printing what the parser reads is
idempotent. The texts below are ones that the printer did not write: they
have comments, other spacing, a tab, a block's first op on its label's
line, `const-1` for `const -1`, quoted symbols, a call to a quoted symbol,
an op that owns a region with a block argument, callsite, fused and
derived locations, and no final line feed. One is of the sum of the core
and the toy dialect. Each test applies the theorem to whatever the parser
reads from the text, and a `#guard` runs the parser: it reads the text, the
printer writes another text, and reading and printing that text gives it
back. One more `#guard` checks that the parser rejects a value defined
again inside a region, the check that `namesUnique` rests on at depth. The
last checks pin the axioms of the theorems to Lean's standard ones.
-/

namespace FirTest

open Fir Core

/-- Formats a text in the dialect `d`: parses it and prints the module that
the parser gives. -/
def fmtIn (d : Dialect) [DialectText d] (t : String) : Option String :=
  match Fir.parse (d := d) t with
  | .ok m => some m.print
  | .error _ => none

/-- The parser accepts `t`, the printer writes another text for it, and
formatting that text gives it back. -/
def fmtIdempotent (d : Dialect) [DialectText d] (t : String) : Bool :=
  match fmtIn d t with
  | some t' => t' != t && fmtIn d t' == some t'
  | none => false

/-! # Comments, spacing and a quoted symbol -/

/-- A function whose symbol, `1`, is not a word, written with comments, a
tab, no spaces where none are needed, `const-1`, a location table with
callsite, fused and derived locations, and no final line feed. -/
def commented : String :=
  "// A function whose symbol is not a word.\n" ++
  "func @\"1\"( %a : i32,%b:i32 )->i32{ // no spaces where none are needed\n" ++
  "^entry:\t%s: i32 = add nsw %a,%b @0  // \"quotes\" in a comment\n" ++
  "  %c: i32=const-1 @1\n" ++
  "  %t: i32 = add %s, %c @0\n" ++
  "  ret %t @0 }\n" ++
  "locs{@0=unknown @1 = \"f.c\":1:2 to 3:4 @2=callsite(@0 at @1) @3=fused(@0,@1)\n" ++
  "@4 = derived( @0 )}"

/-- Whatever the parser reads from `commented` is well formed. -/
theorem commented_wellFormed {m : Module CoreDialect} (h : Fir.parse commented = .ok m) :
    m.WellFormed :=
  Core.parse_wellFormed h

/-- Whatever the parser reads from `commented` reads back from its printed
form, so formatting that form gives it back. -/
theorem commented_reprint {m : Module CoreDialect} (h : Fir.parse commented = .ok m) :
    (Fir.parse (d := CoreDialect) m.print).map Module.print = .ok m.print := by
  rw [Core.parse_print_of_parse h]
  rfl

-- The canonical text drops the comments and keeps the symbol quoted.
#guard fmtIn CoreDialect commented == some
  ("func @\"1\"(%a: i32, %b: i32) -> i32 {\n^entry:\n  %s: i32 = add nsw %a, %b @0\n" ++
    "  %c: i32 = const -1 @1\n  %t: i32 = add %s, %c @0\n  ret %t @0\n}\n\n" ++
    "locs {\n  @0 = unknown\n  @1 = \"f.c\":1:2 to 3:4\n  @2 = callsite(@0 at @1)\n" ++
    "  @3 = fused(@0, @1)\n  @4 = derived(@0)\n}\n")
#guard fmtIdempotent CoreDialect commented

/-! # Branches, calls and regions -/

/-- A function whose symbol is quoted and calls itself, after a branch that
passes an argument, and a function whose op owns a region whose block
defines a value, all on few lines, ending with a comment. -/
def calls : String :=
  "func @\"two words\"(%x: i8) -> i8 {\n" ++
  "^entry: br ^next(%x) @0\n" ++
  "^next(%y: i8):  %r: i8 = call @\"two words\" %y @0\n" ++
  "  ret %r @0\n}\n" ++
  "func @g(){^entry: br { ^inner(%v: i8): ret @0 } @0 }\n" ++
  "locs { @0 = unknown }\n// the end"

/-- Whatever the parser reads from `calls` is well formed. -/
theorem calls_wellFormed {m : Module CoreDialect} (h : Fir.parse calls = .ok m) :
    m.WellFormed :=
  Core.parse_wellFormed h

/-- Whatever the parser reads from `calls` reads back from its printed
form. -/
theorem calls_parse_print {m : Module CoreDialect} (h : Fir.parse calls = .ok m) :
    Fir.parse m.print = .ok m :=
  Core.parse_print_of_parse h

#guard fmtIn CoreDialect calls == some
  ("func @\"two words\"(%x: i8) -> i8 {\n^entry:\n  br ^next(%x) @0\n^next(%y: i8):\n" ++
    "  %r: i8 = call @\"two words\" %y @0\n  ret %r @0\n}\n\n" ++
    "func @g() {\n^entry:\n  br {\n    ^inner(%v: i8):\n      ret @0\n  } @0\n}\n\n" ++
    "locs {\n  @0 = unknown\n}\n")
#guard fmtIdempotent CoreDialect calls

-- A value is defined once in its function, at any depth: the parser
-- rejects `%a` defined again by a block of a region, at its second
-- definition.
#guard rejectedAt (oneFunc "func @f(%a: i8){^e: br { ^i(%a: i8): ret @0 } @0 }") 1 29
  "%a is defined twice"

/-! # Another dialect -/

/-- `FirTest.Mixed`'s module, written on two lines with no spaces where none
are needed: a toy op whose result a core op uses. -/
def mixedSpaced : String :=
  "func @f(%a:i8)->i8,i8{^entry: %m:i8=toy.mask 3 %a @1 %s:i8=add %m,%a @0 ret %m,%s @0}\n" ++
  "locs{@0=unknown @1=name(\"mask\")}"

/-- Every module of the sum of the core and the toy dialect that the parser
gives is well formed, from the laws of the sum's text alone. -/
theorem coreToy_parse_wellFormed {t : String} {m : Module CoreToy} (h : Fir.parse t = .ok m) :
    m.WellFormed :=
  Fir.parse_wellFormed h

/-- Whatever the parser reads from `mixedSpaced` reads back from its printed
form. -/
theorem mixedSpaced_parse_print {m : Module CoreToy} (h : Fir.parse mixedSpaced = .ok m) :
    Fir.parse m.print = .ok m :=
  Fir.parse_print_of_parse h

-- The canonical text is `FirTest.Mixed`'s.
#guard fmtIn CoreToy mixedSpaced == some mixed
#guard fmtIdempotent CoreToy mixedSpaced

/-! # The theorems' axioms -/

/-- info: 'Fir.Text.lex_writable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Text.lex_writable

/--
info: 'Fir.Text.readModule_writable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fir.Text.readModule_writable

/--
info: 'Fir.decodeModule_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fir.decodeModule_wellFormed

/-- info: 'Fir.parse_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.parse_wellFormed

/--
info: 'Fir.parse_print_of_parse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fir.parse_print_of_parse

/--
info: 'Fir.Core.parse_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fir.Core.parse_wellFormed

/--
info: 'Fir.Core.parse_print_of_parse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fir.Core.parse_print_of_parse

end FirTest
