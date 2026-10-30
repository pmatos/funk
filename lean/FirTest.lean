import Fir
import FirRef
import FirRef.Main
import FirTest.Axioms
import FirTest.Parse
import FirTest.Print
import FirTest.Lex

/-!
The Lean tests. Building this library runs their checks. This root module
imports every module of `lean/`, and its last command checks that each of
their declarations, and each of its own, is trusted (ADR-2026-10-30-1452).
Nothing may follow that command, since the check would not see it.
-/

#check_axioms Fir FirRef FirTest
