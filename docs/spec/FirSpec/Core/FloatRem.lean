import VersoManual
import Fir.Core.FloatRem
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the remainders, which renders
`Fir.Core.FloatRem` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Float remainder rules: readable blocks" =>

:::moduleDocs (fingerprint := "11417597167154963418")
:::

:::readable Fir.Core.remainder (fingerprint := "11417597167154963418")
*Definition: the remainder.* For a format $`F` of Lean's model and
$`\nu \in \{\mathrm{near}, \mathrm{trunc}\}`, the remainder of $`x` by
$`y` is

$$`\mathrm{rem}^{\nu}_F(x, y) = \begin{cases} \mathrm{NaN} & \text{if } x \text{ or } y \text{ is a NaN, } x = \pm\infty \text{ or } y = \pm 0 \\ x & \text{if } x \text{ is finite or zero and } y = \pm\infty \\ \pm 0 \text{ with the sign of } x & \text{if } x = \pm 0 \text{ and } y \text{ is finite} \\ \mathrm{normalize}_F(\sigma \cdot r', e, \sigma) & \text{if } x \text{ and } y \text{ are finite} \end{cases}`

In the last case $`x = \sigma \cdot m_x \cdot 2^{e_x}` and
$`|y| = m_y \cdot 2^{e_y}`, with the sign $`\sigma` of $`x`. Both are
written at the smaller exponent $`e = \min(e_x, e_y)`, as the whole
numbers $`a = m_x \cdot 2^{e_x - e}` and $`b = m_y \cdot 2^{e_y - e}`. With
$`q = \lfloor a / b \rfloor` and $`r = a \bmod b`,

$$`r' = \begin{cases} r - b & \text{if } \nu = \mathrm{near} \text{ and } (2r > b \text{ or } (2r = b \text{ and } q \text{ is odd})) \\ r & \text{otherwise} \end{cases}`

So $`\mathrm{rem}^{\mathrm{trunc}}_F(x, y) = x - n \cdot y` with
$`n = \mathrm{trunc}(x / y)`, C's `fmod`, and
$`\mathrm{rem}^{\mathrm{near}}_F(x, y) = x - n \cdot y` with $`n` the
integer nearest $`x / y`, a tie to the even one, IEEE 754's remainder.
$`\mathrm{normalize}_F` is the model's: it writes the integer
$`\sigma \cdot r'` times $`2^e` as a number of the format, and a zero with
the sign $`\sigma` of $`x`. $`|r'| \cdot 2^e` is a multiple of $`2^e`, at
least the smallest exponent of the format, and below $`|y|`, so the
format holds it and $`\mathrm{normalize}_F` does not round. For example,
$`\mathrm{rem}^{\mathrm{near}}(5.5, 2) = -0.5` and
$`\mathrm{rem}^{\mathrm{trunc}}(5.5, 2) = 1.5`.
:::
