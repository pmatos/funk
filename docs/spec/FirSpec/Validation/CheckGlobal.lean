import VersoManual
import Fir.Validation.CheckGlobal
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on checking globals, which renders
`Fir.Validation.CheckGlobal` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Checking globals: readable blocks" =>

:::moduleDocs (fingerprint := "18350642467943192337")
:::

:::readable Fir.InitPiece.decidableInLimits Fir.Global.decidableInLimits Fir.lt_two_pow_iff_shiftRight Fir.Global.problem (fingerprint := "9932863284443257295")
*Definition: deciding a global's limits.* Whether a piece, and a global,
are within the limit can be decided. A unit $`u` is below $`2^w` exactly
when shifting it right by $`w` leaves 0, so the check of a unit computes
no power of two. A problem about the global $`G` names its symbol.
:::

:::readable Fir.InitPiece.problems Fir.InitPiece.problems_eq_nil Fir.InitPiece.decidableFits (fingerprint := "10410528506542569144")
*Definition: the check of a piece.* The problems of a piece of the
global $`G` are: for $`\mathsf{units}~u^*`, "the unit $`u` of the
initializer does not fit in $`U` bits" for the first $`u` that does not;
for $`\mathsf{addr}~s~k`, "the initializer's address of @$`s` names no
global of its table" when none does; and none for $`\mathsf{zeros}~k`. A
piece has no problem exactly when it fits, so fitting can be decided.
:::

:::readable Fir.Global.problems Fir.Global.problems_eq_nil Fir.Global.decidableValid Fir.SymbolTable.globalProblems Fir.SymbolTable.globalProblems_eq_nil (fingerprint := "6721538903503881198")
*Definition: the check of a global.* The problems of a global $`G` are, in
order: one when a number of $`G` is above $`2^{64} - 1`; "the global lives
in memory $`n`, which the data layout does not declare"; "the global is
aligned to $`a` units: an alignment is a power of two no larger than
16777215"; the problems of each piece, in order; and "the initializer
takes $`m` units, more than the global's size, $`z`". A global has no
problem exactly when it is valid, so validity can be decided. The
problems of a symbol table's globals are those of each of its globals, in
its own table, and there are none exactly when each is valid.
:::
