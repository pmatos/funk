import VersoManual
import Fir.Core.FloatFlagLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on dropping fast-math flags, which
renders `Fir.Core.FloatFlagLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Dropping fast-math flags: readable blocks" =>

:::moduleDocs (fingerprint := "14123285982004340023")
:::

:::readable Fir.Core.FastMath.le_none (pin := Fir.Core.FastMath.Le) (fingerprint := "1547956872211176349")
*Theorem: no flags are among every flags.* $`\{\} \le \phi` for all
flags $`\phi`.
:::

:::readable Fir.Core.oneFloat_drop (pin := Fir.Core.oneFloat) (pin := Fir.SetM.IsRefinedBy) (fingerprint := "6782892189452855412")
*Theorem: one float, refined.* When $`t` ends, and every value of $`t` is
a value of $`s` or $`s` may give $`\mathsf{poison}`, then
$`\mathrm{one}(t)` refines $`\mathrm{one}(s)`: every way $`\mathrm{one}(t)`
ends is allowed by a way $`\mathrm{one}(s)` ends.
:::

:::readable Fir.Core.fbinValues_drop Fir.Core.funaryValue_drop Fir.Core.fmaValues_drop Fir.Core.fcmpValues_drop (pin := Fir.Core.fbinValues) (pin := Fir.Core.funaryValue) (pin := Fir.Core.fmaValues) (pin := Fir.Core.fcmpValues) (fingerprint := "984134044064763540")
*Theorem: the rules with fewer flags.* Let $`\phi' \le \phi`. On every
operands, each value that the rule of $`\mathsf{fadd}`, $`\mathsf{fsub}`,
$`\mathsf{fmul}`, $`\mathsf{fdiv}`, $`\mathsf{fneg}`, $`\mathsf{fabs}`,
$`\mathsf{sqrt}` or $`\mathsf{fma}` gives under $`\phi'`, it gives under
$`\phi`, or under $`\phi` it may give $`\mathsf{poison}`. A poison operand
gives poison under both, and defined operands give a float result. The
$`\mathsf{i1}` of $`\mathsf{fcmp}` under $`\phi` is refined by its
$`\mathsf{i1}` under $`\phi'`: it is poison, or the same.
:::

:::readable Fir.Core.fbin_drop Fir.Core.funary_drop Fir.Core.fma_drop Fir.Core.fcmp_drop (pin := Fir.Core.Op.denote?) (fingerprint := "16824028553297313093")
*Theorem: dropping a flag refines the flagged op.* For all flags
$`\phi' \le \phi`, every format and every operands $`\vec a`,

$$`\mathit{op}_{e,m}~\phi'~(\vec a) \sqsupseteq \mathit{op}_{e,m}~\phi~(\vec a)`

for $`\mathit{op}` each of $`\mathsf{fadd}`, $`\mathsf{fsub}`,
$`\mathsf{fmul}`, $`\mathsf{fdiv}`, $`\mathsf{fneg}`, $`\mathsf{fabs}`,
$`\mathsf{sqrt}`, $`\mathsf{fma}`, and $`\mathsf{fcmp}` with every
predicate: every way the op with the flags $`\phi'` may end is allowed by
a way the op with $`\phi` may end, as the section on refinement defines
it. So a pass may drop any flag. Native code, which ignores the flags,
refines the flagged op wherever it refines the op with no flags, since
$`\{\} \le \phi`.
:::
