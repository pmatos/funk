import VersoManual
import Fir.Execution.EffectLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on effect obligations, which renders
`Fir.Execution.EffectLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Effect obligations: readable blocks" =>

:::moduleDocs (fingerprint := "1445801162894727801")
:::

:::readable Fir.NeverUB (fingerprint := "7156262212872704501")
*Definition: never UB.* An op $`o` _never ends in UB_ when, on every
operand vector $`\vec{v}` and for every reason $`r`: if $`o` is not a
terminator, $`\mathsf{ub}~r \notin \mathrm{denote}_o(\vec{v})`, and if it
is a terminator, $`\mathsf{ub}~r \notin \mathrm{exit}_o(\vec{v})`.
:::

:::readable Fir.MakesNoPoison (pin := Fir.HVector.Any) (fingerprint := "1040631717548771490")
*Definition: makes no poison.* An op $`o` that is not a terminator _makes
no poison_ when, on every operand vector $`\vec{v}` with no poison
element, every $`\vec{w}` with
$`\mathsf{ok}~\vec{w} \in \mathrm{denote}_o(\vec{v})` has no poison
element. A terminator gives no results, so it makes none.
:::

:::readable Fir.LawfulDialectEffects (pin := Fir.NeverUB) (pin := Fir.MakesNoPoison) (pin := Fir.TypesValid) (pin := Fir.OwnRuleHas) (fingerprint := "16626236626511120339")
*Definition: a dialect lawful in its effects.* A dialect is _lawful in its
effects_ when its effect declarations are sound: an effect that an op
leaves out, it does not have. For every
{ref "The-fir-specification--Validation--The-general-rules"}[valid] op
instance $`o` that is a terminator or has no callee:

* if $`\mathsf{mayUB} \notin \mathrm{eff}(o)`, then $`o` never ends in UB;
* if $`\mathsf{mayPoison} \notin \mathrm{eff}(o)`, then $`o` makes no poison;
* wherever a run names the dialect's memories by $`\rho`, for every memory
  $`x` of the run: if $`\rho(\mathrm{eff}(o).\mathit{writes})` does not
  hold $`x`, what $`o` runs by its own rule writes no unit of $`x`; if
  $`\rho(\mathrm{eff}(o).\mathit{reads})` does not hold $`x`, it does not
  read $`x`; and if $`\rho(\mathrm{eff}(o).\mathit{allocates})` does not
  hold $`x`, it neither allocates nor frees in $`x`
  ({ref "The-fir-specification--Memory--Memory-obligations"}[memory obligations]).

And for every op $`o`: if $`\mathsf{control} \notin \mathrm{eff}(o)`,
then $`o` is not a terminator.

An op with a callee is left out of all but the last: it runs its callee,
not a rule of its own, and has its callee's effects (ADR-2026-11-02-1514).
$`\mathsf{observable}` has no obligation yet, since a run of M0 has no
trace.
:::
