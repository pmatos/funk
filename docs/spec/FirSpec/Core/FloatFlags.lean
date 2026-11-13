import VersoManual
import Fir.Core.FloatFlags
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the fast-math flag rules, which
renders `Fir.Core.FloatFlags` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Fast-math flag rules: readable blocks" =>

:::moduleDocs (fingerprint := "3854419426322820930")
:::

:::readable Fir.Core.FastMath.Le Fir.Core.FastMath.mayPoison (fingerprint := "173714507355988952")
*Definition: fewer flags.* Flags $`\phi'` are _among_ flags $`\phi`,
$`\phi' \le \phi`, when each of $`\mathsf{nnan}`, $`\mathsf{ninf}` and
$`\mathsf{nsz}` that $`\phi'` sets, $`\phi` sets too. The reserved words
do not count.

Flags _may make poison_ when they set $`\mathsf{nnan}` or
$`\mathsf{ninf}`.
:::

:::readable Fir.Core.isZeroFloat Fir.Core.FastMath.breaks Fir.Core.operandsBreak (fingerprint := "11826833287504903788")
*Definition: a float that breaks the flags.* A float of the model breaks
flags $`\phi` when it is a NaN and $`\phi` sets $`\mathsf{nnan}`, or an
infinity and $`\phi` sets $`\mathsf{ninf}`. Operands $`a_1, \dots, a_k`
of $`\mathsf{float}\langle e,m \rangle` break $`\phi` when one of them,
read as $`\mathrm{unpack}_F(a_i)`, does. In a format the model does not
have, no operand breaks anything. A float is a zero when the model reads
it as $`+0` or $`-0`.
:::

:::readable Fir.Core.flipSign Fir.Core.anySign (fingerprint := "14800455738739591513")
*Definition: either sign.* For a bit $`c` and bits $`b` of
$`\mathsf{float}\langle e,m \rangle`, $`\mathrm{flip}_{e,m}(c, b)` is
$`b` with its sign bit flipped when $`c = 1`, and $`b` when $`c = 0`.
$`\mathrm{anysign}_{e,m}(b)` chooses one bit $`c` and gives the value
$`\mathrm{flip}_{e,m}(c, b)`: $`b` with either sign.
:::

:::readable Fir.Core.flagResult (fingerprint := "5720175455161959666")
*Definition: a result under the flags.* A result $`b` that is not a NaN,
which the model reads as $`u`, becomes under flags $`\phi`

$$`\mathrm{flag}_\phi(b) = \begin{cases} \mathsf{poison} & \text{if } \phi \text{ sets } \mathsf{ninf} \text{ and } u \text{ is an infinity} \\ \mathrm{anysign}_{e,m}(b) & \text{else if } \phi \text{ sets } \mathsf{nsz} \text{ and } u \text{ is a zero} \\ b & \text{otherwise} \end{cases}`

The infinity is judged after rounding, so a result that overflows to an
infinity breaks $`\mathsf{ninf}` too.
:::

:::readable Fir.Core.operandsBreak_nil (fingerprint := "16923337574922155933")
*Theorem: no operands.* No operands break the flags when there are none
to read. The conversions between formats and from integers build their result this
way: as a float result with no flags and no operands to judge, so they
carry no fast-math flags.
:::
