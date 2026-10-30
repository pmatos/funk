import FirRef.PrintAttr
import FirRef.PrintModule
import FirRef.Parse
import FirRef.Validate

/-!
The implementations that `fir-ref` runs in place of the spec's functions
(ADR-2026-10-30-1450). Each module below proves its implementation equal to
a spec function and registers that equation with `@[csimp]`. Lean applies
such a lemma only to code compiled after it, so every module of `FirRef`
that calls the spec's parser or printer imports this one first, through
`FirRef.Utf8`.
-/
