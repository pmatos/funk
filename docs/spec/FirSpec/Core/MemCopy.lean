import VersoManual
import Fir.Core.MemCopy
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the copy and move rules, which
renders `Fir.Core.MemCopy` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Copy and move rules: readable blocks" =>

:::moduleDocs (fingerprint := "12405156472491787047")
:::

:::readable Fir.Core.partlyOverlap (fingerprint := "9681611242270941796")
*Definition: ranges that partly overlap.* The ranges of $`n` units
through the pointers $`p` and $`q` partly overlap when $`p` and $`q` have
the provenance of one allocation, not the absence of one, written
$`\bot`, and different offsets less than $`n` apart:

$$`\mathrm{partly}(p, q, n) \iff \mathrm{prov}(p) = \mathrm{prov}(q) \ne \bot \wedge \mathrm{off}(p) \ne \mathrm{off}(q) \wedge |\mathrm{off}(p) - \mathrm{off}(q)| < n`

Equal ranges do not partly overlap, and neither do ranges in two
allocations or through pointers with no provenance. Whether two ranges
partly overlap depends only on the pointers and $`n`, not on the
memories.
:::

:::readable Fir.Core.poisonCopyPointer Fir.Core.overlapCopy Fir.Core.copyLenRule Fir.Core.memCopyRule (pin := Fir.copyUnits) (pin := Fir.MonadMemory) (pin := Fir.MonadUB) (pin := Fir.MonadChoice) (pin := Fir.Core.CopyKind) (fingerprint := "199355975012138981")
*Definition: the rule of $`\mathsf{memcpy}` and $`\mathsf{memmove}`.*
Let a run's memories have the layout entries $`\ell`, and let the run name
the core's memory $`x` as $`\rho(x)`. For $`\mathsf{memcpy}_N~o~W` or
$`\mathsf{memmove}_N~o~W` on the destination $`p`, the source $`q` and
the length $`l`, in a monad with choice, UB and the
{ref "The-fir-specification--Memory--The-memory-effect"}[memory effect],
the rule of a defined length of $`n` units is:

* if $`n = 0`, nothing: no result, whatever $`p` and $`q` are, poison
  included (the human's ruling of 2026-11-18 on #234, Q1);
* otherwise, if $`p` or $`q` is poison, immediate UB, for the reason "a
  copy or move through a poison pointer";
* otherwise, for $`\mathsf{memcpy}` whose ranges
  {ref "The-fir-specification--Memory--Copy-and-move-rules"}[partly overlap],
  immediate UB, for the reason "a memcpy whose ranges partly overlap";
  equal ranges are allowed (the human's ruling of 2026-11-18 on #234, Q2);
* otherwise the
  {ref "The-fir-specification--Memory--Copies-of-units-in-the-state-layer"}[copy of units]
  of $`n` units of $`\rho(N)` from $`q` to $`p`, each access aligned to
  one unit, with no result. An access that faults is UB for the reason of
  its fault.

For a defined $`l` the rule is that of $`n = \mathrm{unsigned}(l)`. For a
poison $`l` it chooses $`W` bits $`b` and runs the rule of
$`n = \mathrm{unsigned}(b)`: a poison length is UB wherever some length
is (ADR-2026-10-29-2006), and otherwise carries the units of some length.
:::
