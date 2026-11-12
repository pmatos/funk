import FirTest

/-!
The check that every declaration of `lean/` is trusted (ADR-2026-10-30-1452).
`FirTest` imports every module of `lean/`, so this module sees them all. Its
library needs the list of the package's `.lean` files, so a file that nothing
imports reruns the check, even when every other module comes from a warm build.
Nothing may follow the check, since it would not see it.
-/

#check_axioms Fir FirRef FirTest
