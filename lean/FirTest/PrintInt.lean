import FirTest.Print

/-!
Tests of `FirRef.printDecimal`, which `fir-ref` runs in place of the spec's
`printInt` (#41). The checks compare it with core's `Int.repr`, which
`printInt` calls, at the edges of the parts that it splits a number into:
around each power of ten up to `10^300`, so around `10^18`, `10^36` and
`10^72`, where a part is all zeros or all nines, and on numbers with up to
about 17,000 digits. Through `FirTest.Print`, this module imports
`FirRef.Utf8`, as `fir-ref` does, so `Attr.print` runs `printAttr`, which
writes integers with `printDecimal`. `scripts/check-fir-ref.sh test` checks
that `fir-ref` writes a constant of five million digits within a limit on
CPU time. The last check pins the axioms of the proof to Lean's standard
ones.
-/

namespace FirTest

open Fir

/-- `printDecimal` writes `i` and `-i` as `Int.repr` does. -/
def agrees (i : Int) : Bool :=
  FirRef.printDecimal i == i.repr && FirRef.printDecimal (-i) == (-i).repr

#guard (List.range 2000).all fun k => agrees k
#guard (List.range 301).all fun e => [10 ^ e - 1, 10 ^ e, 10 ^ e + 1].all fun n => agrees n
#guard [10 ^ 18 * 7 + 3, 10 ^ 40 + 10 ^ 20, 10 ^ 54 + 5, 10 ^ 90 * 123 + 10 ^ 36 - 1].all agrees
#guard [2 ^ 63 - 1, 2 ^ 63, 2 ^ 64, 2 ^ 127 - 1, 2 ^ 127, 2 ^ 1000, 3 ^ 5000, 7 ^ 20000].all agrees
#guard (Attr.int (-(10 ^ 5000 + 7))).print == "-1" ++ "".pushn '0' 4999 ++ "7"

/--
info: 'FirRef.printInt_eq_printDecimal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms FirRef.printInt_eq_printDecimal

end FirTest
