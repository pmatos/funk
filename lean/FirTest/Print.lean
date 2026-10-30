import FirTest.Parse

/-!
Tests of the printer that `fir-ref` runs: `FirRef.printAttr` and
`FirRef.printModule`, proved equal to the spec's `Attr.print` and
`Module.print` and registered with `@[csimp]` (ADR-2026-10-30-1450).
Through `FirTest.Parse`, this module imports `FirRef.Utf8`, as `fir-ref`
does, so the checks below run those implementations. The check on an
attribute 1,000,000 levels deep needs `printAttr`: the spec's printer
overflows the stack there. The checks on modules compare `printModule`'s
output with texts built here line by line; the spec's printer passes them
too. `scripts/check-fir-ref.sh test` is the check that `fir-ref` runs
`printModule`, on texts that the spec's printer is too slow for.
The last checks pin the axioms of the two proofs to Lean's standard ones.
-/

namespace FirTest

open Fir

/-- An attribute nested `n` levels deep: `h(h(x, 1), 1)` for 2. -/
def deepAttr (n : Nat) : Attr := Nat.repeat (fun a => .app "h" [a, .int 1]) n (.word "x")

#guard (deepAttr 2).print == "h(h(x, 1), 1)"
#guard (deepAttr 1000000).print.length == 6 * 1000000 + 1
#guard (Attr.app "f" [.str "a\"b", .sym "1", .sym "s", .app "g" [], .int (-5)]).print ==
  "f(\"a\\\"b\", @\"1\", @s, g(), -5)"

/-- A function whose entry block holds an op that owns a region, whose one
block holds an op that owns a region, and so on, `n` levels deep. -/
def nested (n : Nat) : Module CoreDialect :=
  let ret : Operation CoreDialect := ⟨[], .ret [], [], [], [], 0⟩
  let body := Nat.repeat (fun os => [⟨[], .br, [], [], [⟨[⟨"b", [], os⟩]⟩], 0⟩]) n [ret]
  ⟨[.func ⟨"f", [], [], ⟨[⟨"e", [], body⟩]⟩⟩], [(0, .unknown)]⟩

/-- The canonical text of `nested n`, line by line. -/
def nestedText (n : Nat) : String :=
  let line (k : Nat) (s : String) := "".pushn ' ' k ++ s ++ "\n"
  "func @f() {\n^e:\n" ++
    String.join ((List.range n).map fun i => line (2 + 4 * i) "br {" ++ line (4 + 4 * i) "^b:") ++
    line (2 + 4 * n) "ret @0" ++
    String.join ((List.range n).reverse.map fun i => line (2 + 4 * i) "} @0") ++
    "}\n\nlocs {\n  @0 = unknown\n}\n"

#guard (nested 0).print == nestedText 0 && (nested 1).print == nestedText 1
#guard (nested 1000).print == nestedText 1000
#guard roundTrips (nestedText 300)

/-- A block of `n` constants, then `ret`. -/
def flat (n : Nat) : String :=
  func ((List.range n).map (s!"%c{·}: i32 = const 0 @0") ++ ["ret %a @0"])

#guard roundTrips (flat 10000)

/--
info: 'FirRef.print_eq_printAttr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms FirRef.print_eq_printAttr

/--
info: 'FirRef.print_eq_printModule' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms FirRef.print_eq_printModule

end FirTest
