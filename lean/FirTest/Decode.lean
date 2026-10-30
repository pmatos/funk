import FirTest.Print

/-!
Tests of the decoder that `fir-ref` runs: `FirRef.decodeModule`, proved
equal to the spec's `Text.decodeModule` and registered with `@[csimp]`, and
`FirRef.parse`, which runs in place of `Fir.parse` and calls it
(ADR-2026-10-30-1450). Through `FirTest.Print`, this module imports
`FirRef.Utf8`, as `fir-ref` does, so the checks below run those
implementations, and so do the parser's checks in `FirTest.Parse`.

The syntax trees are built here, not read from text, since the spec's
readers still take stack per level of nesting. The checks on regions nested
1,000,000 levels deep, on a type 1,000,000 levels deep, on a block of
3,000,000 ops and on an op with 3,000,000 operands need the decoder's loops
and its copy of `decodeType`: without `decodeModule_eq_decodeModule`, the
spec's decoder overflows the stack on each, and the build fails. The flat
checks take 3,000,000 because at 1,000,000 the spec's decoder still fits in
the stack that Lean gives these checks.
The checks on smaller trees compare the decoded module with a text built
line by line. The last checks pin the axioms of the two theorems to Lean's
standard ones.
-/

namespace FirTest

open Fir Fir.Text

/-- A position in a text. -/
def pos (line col : Nat) : TextPos := ⟨line, col⟩

/-- `%n: i32` as written, at line 1. -/
def sdef (n : String) : SDef := ⟨n, pos 1 1, .word "i32", pos 1 5⟩

/-- An op as written, with no attributes or successors, and its location
reference `@0`. -/
def sop (results : List SDef) (name : String) (operands : List (Name × TextPos))
    (regions : List SRegion) : SOp :=
  ⟨results, name, pos 1 1, [], operands, [], regions, 0⟩

/-- A module with one function `@f(params) -> results`, whose body is one
block that holds `ops`, and the location table of `@0`. -/
def sfunc (params : List SDef) (results : List (Attr × TextPos)) (label : Name)
    (ops : List SOp) : SModule :=
  ⟨[⟨"func", pos 1 1, "f", params, results, [], .blocks [⟨label, [], ops⟩]⟩], [(0, .unknown)]⟩

/-- `inner` inside `n` levels of regions: the block of each region holds a
`br` that owns the next region, as in `nested`. -/
def deepRegions (n : Nat) (params : List SDef) (inner : SOp) : SModule :=
  sfunc params [] "e" (Nat.repeat (fun os => [sop [] "br" [] [⟨[⟨"b", [], os⟩]⟩]]) n [inner])

/-- Decodes with the core dialect. -/
def decodeCore (m : SModule) : Except ParseError (Module CoreDialect) := Text.decodeModule m

/-- The module decodes and prints as `text`. -/
def decodesAs (m : SModule) (text : String) : Bool :=
  match decodeCore m with
  | .ok m => m.print == text
  | .error _ => false

/-- The module is rejected at `p`, for the reason `reason`. -/
def rejectedFor (m : SModule) (p : TextPos) (reason : String) : Bool :=
  match decodeCore m with
  | .error e => e.pos == p && e.reason == reason
  | .ok _ => false

/-- `ret`, as written. -/
def sret : SOp := sop [] "ret" [] []

-- Regions nested 1,000 levels deep decode to `nested 1000`, and 1,000,000 deep decode.
#guard decodesAs (deepRegions 0 [] sret) (nestedText 0)
#guard decodesAs (deepRegions 1000 [] sret) (nestedText 1000)
#guard (decodeCore (deepRegions 1000000 [] sret)).toBool

-- The innermost op's operand is undefined, 1,000,000 levels deep.
#guard rejectedFor (deepRegions 1000000 [] (sop [] "ret" [("x", pos 7 9)] []))
  (pos 7 9) "value %x is not defined in @f"

-- The innermost op defines a parameter of the function again.
#guard rejectedFor
  (deepRegions 1000000 [sdef "v"] (sop [⟨"v", pos 8 3, .word "i32", pos 8 7⟩] "ret" [] []))
  (pos 8 3) "value %v is defined twice"

/-- A function whose entry block holds an op with two regions of two blocks
each, between other ops, and a second block. -/
def bushy : Module CoreDialect :=
  let c (n : Name) : Operation CoreDialect := ⟨[(n, .int 8)], .const 8 1, [], [], [], 0⟩
  let ret (xs : List Name) : Operation CoreDialect :=
    ⟨[], .ret (xs.map fun _ => .int 8), xs, [], [], 0⟩
  let blk (l : Name) : Block CoreDialect :=
    ⟨l, [("p" ++ l, .int 8)], [c ("c" ++ l), ret ["p" ++ l]]⟩
  let region (k : Name) : Region CoreDialect := ⟨[blk (k ++ "1"), blk (k ++ "2")]⟩
  let br : Operation CoreDialect := ⟨[], .br, [], [], [region "a", region "b"], 0⟩
  let body : List (Block CoreDialect) :=
    [⟨"e", [], [c "y", br, c "z", ret ["x"]]⟩, ⟨"e2", [], [ret []]⟩]
  ⟨[.func ⟨"f", [("x", .int 8)], [], ⟨body⟩⟩], [(0, .unknown)]⟩

-- Its text reads back in order through `FirRef.parse`.
#guard roundTrips bushy.print && (bushy.print.splitOn "^").length == 7

/-- A block of `n` constants, then `ret %a`, as written: `flat n`. -/
def flatTree (n : Nat) : SModule :=
  sfunc [sdef "a"] [(.word "i32", pos 1 1)] "entry"
    ((List.range n).map (fun i => ⟨[sdef s!"c{i}"], "const", pos 1 1, [.int 0], [], [], [], 0⟩) ++
      [sop [] "ret" [("a", pos 1 1)] []])

#guard decodesAs (flatTree 1000) (flat 1000)

/-- The number of ops in the first block of the first function. -/
def opCount : Except ParseError (Module CoreDialect) → Nat
  | .ok ⟨[.func ⟨_, _, _, ⟨[⟨_, _, os⟩]⟩⟩], _⟩ => os.length
  | _ => 0

-- A block of 3,000,000 ops.
#guard opCount (decodeCore (sfunc [] [] "e" (List.replicate 3000000 (sop [] "br" [] [])))) ==
  3000000

-- An op with 3,000,000 operands.
#guard opCount (decodeCore
  (sfunc [sdef "a"] [] "e" [sop [] "ret" (List.replicate 3000000 ("a", pos 1 1)) []])) == 1

-- A type 1,000,000 levels deep does not decode, and the reason prints it.
#guard match decodeCore (sfunc [] [(deepAttr 1000000, pos 2 3)] "e" []) with
  | .error e => e.pos == pos 2 3 && e.reason.length == 5 + (6 * 1000000 + 1) + 16
  | .ok _ => false

/--
info: 'FirRef.decodeModule_eq_decodeModule' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms FirRef.decodeModule_eq_decodeModule

/--
info: 'FirRef.parse_eq_parse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms FirRef.parse_eq_parse

end FirTest
