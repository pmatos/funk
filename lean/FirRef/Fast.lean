import FirRef.PrintInt
import FirRef.PrintAttr
import FirRef.PrintModule
import FirRef.Parse
import FirRef.Dominance
import FirRef.LocTable
import FirRef.Validate
import FirRef.Lex.Arg

/-!
The implementations that `fir-ref` runs in place of the spec's functions
(ADR-2026-10-30-1450). Each module below proves its implementation equal to
a spec function and registers that equation with `@[csimp]`;
`FirRef.Lex.Arg` proves its own equal to `fir-ref run`'s reading of an
argument by the spec's lexer. Lean applies such a lemma only to code
compiled after it, so every module of `FirRef` that calls the spec's
parser, printer or validation check, or reads an argument, imports this
one first, through `FirRef.Utf8`. The run modes' implementations name the
core dialect, so `FirRef.Run` registers their theorems instead, before
`runBytes` (ADR-2026-11-04-2132).
-/
