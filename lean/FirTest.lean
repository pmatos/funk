import Fir
import FirRef
import FirRef.Main
import FirTest.Axioms
import FirTest.Parse

/-!
The Lean tests. Building this library runs their checks, and this root
module, which imports every module that Lake builds in `lean/`, then checks
that each of their declarations is trusted (ADR-2026-10-30-1452).
-/

#check_axioms Fir FirRef FirTest
