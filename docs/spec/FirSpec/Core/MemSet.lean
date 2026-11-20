import VersoManual
import Fir.Core.MemSet
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the fill rules, which
renders `Fir.Core.MemSet` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Fill rules: readable blocks" =>

:::moduleDocs (fingerprint := "9511657453676319509")
:::

:::readable Fir.Core.setUnit (fingerprint := "18215717151201592706")
*Definition: the unit of a fill.* The unit of $`u` bits that a fill
writes of a value $`v` of $`\mathsf{i}V` is the bits of $`v`, cut to their
low $`u` bits or padded with zeros to $`u` bits, and a poison unit for
poison:

$$`\mathrm{setunit}_u(v) = \begin{cases} \mathsf{bits}(v \bmod 2^u) & \text{if } v \text{ is defined} \\ \mathsf{poison} & \text{if } v \text{ is poison} \end{cases}`

The {ref "The-fir-specification--Validation--The-data-layout___s-rules"}[data layout]
asks that $`V = u`, so a valid fill writes the bits of $`v` themselves;
the cut and the padding only make the rule total for a module that
`fir-ref run` runs without validating it.
:::

:::readable Fir.Core.poisonSetPointer Fir.Core.setUnits Fir.Core.setLenRule Fir.Core.memSetRule (pin := Fir.MonadMemory) (pin := Fir.MonadUB) (pin := Fir.MonadChoice) (pin := Fir.Core.setUnit) (fingerprint := "10548905757158332906")
*Definition: the rule of $`\mathsf{memset}`.* Let a run's memories have
the layout entries $`\ell`, and let the run name the core's memory $`x` as
$`\rho(x)`. For $`\mathsf{memSet}_N~o~V~W` on the destination $`p`, the
value $`v` and the length $`l`, in a monad with choice, UB and the
{ref "The-fir-specification--Memory--The-memory-effect"}[memory effect],
the rule of a defined length of $`n` units is:

* if $`n = 0`, nothing: no result, whatever $`p` is, poison included (the
  human's ruling of 2026-11-18 on #234, Q1);
* otherwise, if $`p` is poison, immediate UB, for the reason "a memset
  through a poison pointer";
* otherwise the store through $`p` of $`n` copies of
  $`\mathrm{setunit}_u(v)` in $`\rho(N)`, whose units are $`u` bits wide,
  aligned to one unit, with no result. An access that faults is UB for
  the reason of its fault. A poison $`v` writes poison units and is not
  UB.

For a defined $`l` the rule is that of $`n = \mathrm{unsigned}(l)`. For a
poison $`l` it chooses $`W` bits $`b` and runs the rule of
$`n = \mathrm{unsigned}(b)`: a poison length is UB wherever some length
is (ADR-2026-10-29-2006; the human's ruling of 2026-11-19 on #234), and
otherwise writes the units of some length.
:::

:::readable Fir.Core.memSetRule_map (pin := Fir.MonadMorphism.KeepsChoiceUB) (fingerprint := "918207579931522484")
*Theorem: a morphism maps the rule.* A monad morphism that keeps choice,
UB and stores maps the rule of $`\mathsf{memset}` in the one monad to the
same rule in the other, on every operand.
:::
