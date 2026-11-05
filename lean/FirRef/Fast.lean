import FirRef.PrintInt
import FirRef.PrintAttr
import FirRef.PrintModule
import FirRef.Parse
import FirRef.Dominance
import FirRef.Validate

/-!
The implementations that `fir-ref` runs in place of the spec's functions
(ADR-2026-10-30-1450). Each module below proves its implementation equal to
a spec function and registers that equation with `@[csimp]`. Lean applies
such a lemma only to code compiled after it, so every module of `FirRef`
that calls the spec's parser, printer or validation check imports this one
first, through `FirRef.Utf8`. The run modes' implementations name the core
dialect, so `FirRef.Run` registers their theorems instead, before `runBytes`
(ADR-2026-11-04-2132).
-/
