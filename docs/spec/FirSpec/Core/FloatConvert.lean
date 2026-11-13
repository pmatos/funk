import VersoManual
import Fir.Core.FloatConvert
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the rules of the conversions between
float formats, which renders `Fir.Core.FloatConvert` (ADR-2026-11-05-2012).
Each block explains declarations of that module and pins their
fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "Format conversion rules: readable blocks" =>

:::moduleDocs (fingerprint := "5208776516006223411")
:::

:::readable Fir.Core.convertModel (fingerprint := "8486092060311938938")
*Definition: a number of the model in another format.* For every format
$`G` of Lean's float model and every number $`u` of the model,
$`\mathrm{conv}_G(u)` is $`\mathrm{round}_G(s, m, x)` when $`u` is the
finite number $`(-1)^s \cdot m \cdot 2^x`: the model's rounding of it into
$`G`, to nearest, ties to even, which gives a zero of its sign when it is
too small for $`G` and, once packed, an infinity of its sign when it is too
large. A zero, an infinity and the NaN are themselves.
:::

:::readable Fir.Core.convertBits (pin := Fir.Core.convertModel) (fingerprint := "11141505869315033033")
*Definition: the conversion on bits.* For every two formats $`F` and $`G`
of the model and $`a \in \mathbb{B}^{|F|}`,
$`\mathrm{convert}_{F,G}(a) = \mathrm{pack}_G(\mathrm{conv}_G(\mathrm{unpack}_F(a)))`:
the number that $`a` encodes in $`F`, in $`G`, written as bits of $`G`.
:::

:::readable Fir.Core.convertFloat (pin := Fir.Core.floatResult) (pin := Fir.Core.convertModel) (fingerprint := "9396562543172022913")
*Definition: the rule of $`\mathsf{fpext}` and $`\mathsf{fptrunc}`.* For
every two formats $`\mathsf{float}\langle e,m \rangle` and
$`\mathsf{float}\langle e',m' \rangle`, whose formats in Lean's model are
$`F` and $`G`, and $`a \in \mathbb{B}^{1+e+m}`:

$$`\mathsf{fpext}_{e,m,e',m'}(a) = \mathsf{fptrunc}_{e,m,e',m'}(a) = \mathrm{result}^{\emptyset}_{e',m'}([\,], \mathrm{conv}_G(\mathrm{unpack}_F(a)))`

and both give $`\mathsf{poison}` on $`\mathsf{poison}`. The
{ref "The-fir-specification--Execution--Float-arithmetic-rules"}[float result],
with no fast-math flags, which the conversions do not carry, packs a
number as bits of $`G`, and gives any NaN of
$`\mathsf{float}\langle e',m' \rangle` for a NaN, which a NaN operand
gives. When the source format is not one of the model's, the number is
the NaN, so that the rule is total. Neither rule is ever UB. The two ops
differ only in the pairs of formats that
{ref "The-fir-specification--Validation--Core-rules"}[validation]
lets them take: $`\mathsf{fpext}` a target that holds every value of the
source, so that $`\mathrm{conv}_G` never rounds, and $`\mathsf{fptrunc}`
every other.
:::

:::readable Fir.Core.round_isNaN Fir.Core.convertModel_isNaN Fir.Core.convertFloat_valid (pin := Fir.Core.convertFloat) (pin := Fir.Core.convertBits) (fingerprint := "6625690192451878486")
*Theorems: a conversion of a number chooses nothing.* The model's rounding
of a finite number is never a NaN, so $`\mathrm{conv}_G(u)` is a NaN
exactly when $`u` is. So at every two formats that the model has, which
are the formats that validation accepts, each rule gives on an operand
that is not a NaN one result, the bits $`\mathrm{convert}_{F,G}(a)`, with
no choice. Only a NaN operand, or a format that validation rejects, makes
the float result choose a NaN.
:::
