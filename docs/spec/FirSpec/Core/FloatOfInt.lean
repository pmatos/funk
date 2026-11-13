import VersoManual
import Fir.Core.FloatOfInt
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the rules of the conversions from
integers to floats, which renders `Fir.Core.FloatOfInt`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "Conversion rules: readable blocks" =>

:::moduleDocs (fingerprint := "15129204928942578814")
:::

:::readable Fir.Core.intOfBits (fingerprint := "9829352279126429626")
*Definition: the integer that bits hold.* For every width $`N` and
$`a \in \mathbb{B}^N`, $`\mathrm{signed}(a)` is $`a` read in two's
complement, from $`-2^{N-1}` to $`2^{N-1} - 1`, and $`\mathrm{unsigned}(a)`
is $`a` read as a binary number, from $`0` to $`2^N - 1`. So the $`\mathsf{i8}`
value with every bit set is $`-1` signed and $`255` unsigned.
:::

:::readable Fir.Core.intToFloat (pin := Fir.Core.floatResult) (fingerprint := "9086376024549251221")
*Definition: the rules of $`\mathsf{sitofp}` and $`\mathsf{uitofp}`.* For
every width $`N`, every format $`\mathsf{float}\langle e,m \rangle`, whose
format in Lean's model is $`F`, and $`a \in \mathbb{B}^N`:

$$`\mathsf{sitofp}_{N,e,m}(a) = \mathrm{result}^{\emptyset}_{e,m}([\,], \mathrm{ofInt}_F(\mathrm{signed}(a)))`

$$`\mathsf{uitofp}_{N,e,m}(a) = \mathrm{result}^{\emptyset}_{e,m}([\,], \mathrm{ofInt}_F(\mathrm{unsigned}(a)))`

and both give $`\mathsf{poison}` on $`\mathsf{poison}`.
$`\mathrm{ofInt}_F(k)` is the model's number nearest the integer $`k`, a
tie to the one whose mantissa is even, an infinity of $`k`'s sign when
that number is too large for the format, and $`+0` when $`k = 0`; the
{ref "The-fir-specification--Execution--Float-arithmetic-rules"}[float result]
packs it as bits, with no fast-math flags, which the conversions do not
carry. Neither rule is ever UB.
:::

:::readable Fir.Core.roundWithAccuracy_isNaN Fir.Core.ofInt_isNaN Fir.Core.intToFloat_valid (pin := Fir.Core.intToFloat) (fingerprint := "2360592073741922987")
*Theorems: a conversion chooses nothing.* The model's rounding of a
finite number gives a zero or a finite number, never a NaN, so
$`\mathrm{ofInt}_F(k)` is never a NaN. So at every format that the model
has, $`e \ge 2` and $`m \ge 1`, which are the formats that validation
accepts, each rule gives on a value one result, the bits
$`\mathrm{pack}_F(\mathrm{ofInt}_F(k))`, with no choice. Only at a format
that validation rejects does the float result choose a NaN, so that the
rules are total.
:::
