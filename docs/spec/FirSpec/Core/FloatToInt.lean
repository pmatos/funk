import VersoManual
import Fir.Core.FloatToInt
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the rules of the conversions from
floats to integers, which renders `Fir.Core.FloatToInt`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "Integer conversion rules: readable blocks" =>

:::moduleDocs (fingerprint := "11052021520276441462")
:::

:::readable Fir.Core.truncInt (fingerprint := "13139265911876038169")
*Definition: the integer of a number, truncated.* For a number $`u` of
Lean's float model, $`\mathrm{trunc}(u)` is $`0` when $`u` is a zero of
either sign, the integer that the model's $`\mathrm{roundToInt}` gives
when $`u` is finite, which cuts the fraction off toward zero, so
$`\mathrm{trunc}(2.7) = 2` and $`\mathrm{trunc}(-2.7) = -2`, and nothing
when $`u` is an infinity or a NaN.
:::

:::readable Fir.Core.intFits (fingerprint := "10314557250704728666")
*Definition: an integer that a width holds.* For every width $`N` and
integer $`k`, $`\mathrm{fits}_N(\mathit{true}, k)` holds when
$`-2^N \le 2k < 2^N`, that is $`-2^{N-1} \le k \le 2^{N-1} - 1` for
$`N \ge 1`, and $`\mathrm{fits}_N(\mathit{false}, k)` when
$`0 \le k < 2^N`. At $`N = 0` only $`0` fits.
:::

:::readable Fir.Core.floatToInt (fingerprint := "4881016367478082761")
*Definition: the rules of $`\mathsf{fptosi}` and $`\mathsf{fptoui}`.* For
every format $`\mathsf{float}\langle e,m \rangle`, whose format in Lean's
model is $`F`, every width $`N`, and $`a \in \mathbb{B}^{1+e+m}`, let
$`k = \mathrm{trunc}(\mathrm{unpack}_F(a))`. Then

$$`\mathsf{fptosi}_{e,m,N}(a) = \begin{cases} \mathrm{bits}_N(k) & \text{if } k \text{ is an integer and } \mathrm{fits}_N(\mathit{true}, k) \\ \mathsf{poison} & \text{otherwise} \end{cases}`

and $`\mathsf{fptoui}_{e,m,N}` likewise with $`\mathrm{fits}_N(\mathit{false}, k)`,
where $`\mathrm{bits}_N(k)` is $`k` in two's complement, modulo $`2^N`.
Both give $`\mathsf{poison}` on $`\mathsf{poison}`, and at a format that
the model does not have, $`e < 2` or $`m = 0`, which validation rejects.
So an infinity, a NaN and an integer out of range give poison, and
neither rule chooses or is ever UB. This is IEEE 754's
$`\mathrm{convertToIntegerTowardZero}`, as the human ruled on 2026-11-12.
:::
