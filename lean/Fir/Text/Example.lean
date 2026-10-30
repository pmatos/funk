import Fir.Core.Text
import Fir.Text.Print

/-!
# An example

The function `@sum` adds the integers from `0` up to, but not including,
`%n`, and `@sum10` calls it. In the canonical text:

```
func @sum(%n: i32) -> i32 {
^entry:
  %zero: i32 = const 0 @1
  br ^loop(%zero, %zero) @1
^loop(%i: i32, %acc: i32):
  %done: i1 = icmp sge %i, %n @2
  cond_br %done, ^exit(%acc), ^body @2
^body:
  %acc1: i32 = add nsw %acc, %i @3
  %one: i32 = const 1 @3
  %i1: i32 = add nsw %i, %one @3
  br ^loop(%i1, %acc1) @3
^exit(%r: i32):
  ret %r @4
}

func @sum10() -> i32 {
^entry:
  %ten: i32 = const 10 @5
  %s: i32 = call @sum %ten @6
  ret %s @0
}

locs {
  @0 = unknown
  @1 = "sum.c":2:3 to 2:14
  @2 = "sum.c":3:10 to 3:15
  @3 = "sum.c":4:5 to 4:16
  @4 = "sum.c":6:3 to 6:13
  @5 = "main.c":2:19 to 2:20
  @6 = "main.c":2:15 to 2:21
}
```

`%n` is a parameter, so it is the entry block's argument, and the entry block
dominates every block: `^loop` uses `%n` without being passed it. The `ret` of
`@sum10` has an unknown location, which is an entry of the table like any
other. Each range ends just after its last byte.

Below is the same module as abstract syntax, and a check, run on every build,
that it prints as the text above.
-/

namespace Fir.Example

open Core

/-- An op of the core dialect, with no regions. -/
def op (results : List (Name × Ty)) (o : Op) (operands : List Name) (loc : LocRef)
    (succs : List Succ := []) : Operation CoreDialect :=
  { results, op := o, operands, succs, regions := [], loc }

/-- `@sum`. -/
def sum : Func CoreDialect where
  name := "sum"
  params := [("n", i 32)]
  results := [i 32]
  body := ⟨[
    ⟨"entry", [], [
      op [("zero", i 32)] (.const 32 0) [] 1,
      op [] .br [] 1 [⟨"loop", ["zero", "zero"]⟩]]⟩,
    ⟨"loop", [("i", i 32), ("acc", i 32)], [
      op [("done", i 1)] (.icmp .sge 32) ["i", "n"] 2,
      op [] .condBr ["done"] 2 [⟨"exit", ["acc"]⟩, ⟨"body", []⟩]]⟩,
    ⟨"body", [], [
      op [("acc1", i 32)] (.add 32 { nsw := true }) ["acc", "i"] 3,
      op [("one", i 32)] (.const 32 1) [] 3,
      op [("i1", i 32)] (.add 32 { nsw := true }) ["i", "one"] 3,
      op [] .br [] 3 [⟨"loop", ["i1", "acc1"]⟩]]⟩,
    ⟨"exit", [("r", i 32)], [
      op [] (.ret [i 32]) ["r"] 4]⟩]⟩

/-- `@sum10`. -/
def sum10 : Func CoreDialect where
  name := "sum10"
  params := []
  results := [i 32]
  body := ⟨[
    ⟨"entry", [], [
      op [("ten", i 32)] (.const 32 10) [] 5,
      op [("s", i 32)] (.call "sum" [i 32] [i 32]) ["ten"] 6,
      op [] (.ret [i 32]) ["s"] 0]⟩]⟩

/-- The module. -/
def sumModule : Module CoreDialect where
  items := [.func sum, .func sum10]
  locs := [
    (0, .unknown),
    (1, .range "sum.c" 2 3 2 14),
    (2, .range "sum.c" 3 10 3 15),
    (3, .range "sum.c" 4 5 4 16),
    (4, .range "sum.c" 6 3 6 13),
    (5, .range "main.c" 2 19 2 20),
    (6, .range "main.c" 2 15 2 21)]

#guard sumModule.print == "\n".intercalate [
  "func @sum(%n: i32) -> i32 {",
  "^entry:",
  "  %zero: i32 = const 0 @1",
  "  br ^loop(%zero, %zero) @1",
  "^loop(%i: i32, %acc: i32):",
  "  %done: i1 = icmp sge %i, %n @2",
  "  cond_br %done, ^exit(%acc), ^body @2",
  "^body:",
  "  %acc1: i32 = add nsw %acc, %i @3",
  "  %one: i32 = const 1 @3",
  "  %i1: i32 = add nsw %i, %one @3",
  "  br ^loop(%i1, %acc1) @3",
  "^exit(%r: i32):",
  "  ret %r @4",
  "}",
  "",
  "func @sum10() -> i32 {",
  "^entry:",
  "  %ten: i32 = const 10 @5",
  "  %s: i32 = call @sum %ten @6",
  "  ret %s @0",
  "}",
  "",
  "locs {",
  "  @0 = unknown",
  "  @1 = \"sum.c\":2:3 to 2:14",
  "  @2 = \"sum.c\":3:10 to 3:15",
  "  @3 = \"sum.c\":4:5 to 4:16",
  "  @4 = \"sum.c\":6:3 to 6:13",
  "  @5 = \"main.c\":2:19 to 2:20",
  "  @6 = \"main.c\":2:15 to 2:21",
  "}",
  ""]

/-!
# More printing checks

An op with a region, a symbol that is not a word, and an applied attribute
with no arguments. No core op has a region, so the region below is only
there to check the printer's layout, which is the same for every dialect.
-/

#guard Operation.print 2 { op [] .br [] 7 with regions := [⟨[⟨"inner", [], [op [] (.ret []) [] 0]⟩]⟩] } ==
  "  br {\n    ^inner:\n      ret @0\n  } @7\n"

#guard Func.print (d := CoreDialect)
    ⟨"1", [], [], ⟨[⟨"entry", [], [op [] (.call "a b" [] []) [] 0, op [] (.ret []) [] 0]⟩]⟩⟩ ==
  "func @\"1\"() {\n^entry:\n  call @\"a b\" @0\n  ret @0\n}\n"

#guard (Attr.app "h" []).print == "h()" && (Attr.word "h").print == "h"

end Fir.Example
