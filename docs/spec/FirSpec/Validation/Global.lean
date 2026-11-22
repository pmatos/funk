import VersoManual
import Fir.Validation.Global
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a global's rules, which renders
`Fir.Validation.Global` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "A global's rules: readable blocks" =>

:::moduleDocs (fingerprint := "6916921189686994937")
:::

:::readable Fir.Global.named? Fir.InitPiece.unitCount Fir.Global.initUnits (fingerprint := "15130458197272923178")
*Definition: the units of an initializer.* Among the globals $`gs` of a
table, $`\mathrm{named?}(gs, s)` is the first with the symbol $`s`. In the
memory $`n` of a module whose data layout is $`\ell`, a piece
$`\mathsf{units}~u^*` takes one unit for each $`u`, $`\mathsf{zeros}~k`
takes $`k`, and $`\mathsf{addr}~s~k` takes the units of one pointer of the
memory of the global $`s` names, as a pointer stored in $`n` does
(ADR-2026-11-12-2125), and none when no global of $`gs` has that symbol.
The units of a global's initializer are those of its pieces, summed.
:::

:::readable Fir.InitPiece.Fits Fir.Global.Valid Fir.Module.GlobalsValid (fingerprint := "3370090529115352604")
*Definition: a valid global.* A global $`G` of the memory $`n` is valid as
an item of a table whose globals are $`gs`, in a module whose data layout
is $`\ell`, when:

* its numbers are within the limit;
* $`\ell` declares $`n`;
* its alignment is a power of two no larger than $`2^{24} - 1`;
* each unit $`u` of its initializer is below $`2^U`, where $`U` is the
  unit width of $`n`, and each address names a global of $`gs`: an item
  names only items of its own table (ADR-2026-11-10-1510); a function's
  address, an allocation of kind `function` (the human's ruling of
  2026-11-19 on #235), waits until runs make those allocations;
* its initializer takes no more units than its size.

The units past the initializer are a run's question, not validation's. A
module's globals are valid when each global of each of its symbol tables
is valid as an item of that table.
:::
