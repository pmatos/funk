import VersoManual
import Fir.Core.FloatOpTextLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on how the float ops read back from
their spelling, which renders `Fir.Core.FloatOpTextLaws`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "The float ops read back: readable blocks" =>

:::moduleDocs (fingerprint := "14909725246307615234")
:::

:::readable Fir.Core.decodeFBin_eq Fir.Core.decodeFUnary_eq Fir.Core.decodeFma_eq (pin := Fir.Core.decodeFBin) (pin := Fir.Core.decodeFUnary) (pin := Fir.Core.decodeFma) (fingerprint := "17736563499205844938")
*Theorems: a float op of arithmetic decodes only from its own spelling.*
If $`\mathsf{fadd}`, $`\mathsf{fsub}`, $`\mathsf{fmul}`,
$`\mathsf{fdiv}`, $`\mathsf{frem}` or $`\mathsf{fmod}` decodes from the attributes $`a^*` and the types $`t^*`
and $`r^*`, as the section on
{ref "The-fir-specification--Text-format--Float-arithmetic-in-text"}[float arithmetic in text]
reads it, the op it gives has its name, the attributes $`a^*` and the
operand and result types $`t^*` and $`r^*`; and the same holds of
$`\mathsf{fneg}`, $`\mathsf{fabs}`, $`\mathsf{sqrt}` and $`\mathsf{fma}`.
Each op's attributes are the words of its fast-math flags and then its
own, its rounding mode for an op that rounds, and the words that reading
takes back put the attributes back together. The proof that every core op reads back, in the next section, uses them
for these ops.
:::

:::readable Fir.Core.decodeBitcast_eq (pin := Fir.Core.decodeBitcast) (fingerprint := "4884971220709374630")
*Theorem: a bit cast decodes only from its own spelling.* If
$`\mathtt{bitcast}` decodes from the attributes $`a^*` and the types
$`t^*` and $`r^*`, the op it gives, in either direction, is written
$`\mathtt{bitcast}`, has no attributes, so $`a^*` is empty, and has the
operand and result types $`t^*` and $`r^*`.
:::

:::readable Fir.Core.decodeIntToFloat_eq (pin := Fir.Core.decodeIntToFloat) (fingerprint := "16410626810055295878")
*Theorem: a conversion from an integer decodes only from its own
spelling.* If $`\mathtt{sitofp}` or $`\mathtt{uitofp}` decodes from the
attributes $`a^*` and the types $`t^*` and $`r^*`, the op it gives is
written with that name, has the attributes $`a^*`, which are
$`[\mathtt{round}(r)]` for the mode $`r` it carries, and has the operand
and result types $`t^*` and $`r^*`.
:::

:::readable Fir.Core.decodeFpext_eq Fir.Core.decodeFptrunc_eq (pin := Fir.Core.decodeFpext) (pin := Fir.Core.decodeFptrunc) (fingerprint := "12704849528167814365")
*Theorems: a conversion between formats decodes only from its own
spelling.* If $`\mathtt{fpext}` or $`\mathtt{fptrunc}` decodes from the
attributes $`a^*` and the types $`t^*` and $`r^*`, the op it gives is
written with that name, has the attributes $`a^*`, which are none for
$`\mathtt{fpext}` and $`[\mathtt{round}(r)]` for $`\mathtt{fptrunc}` with the mode $`r`,
and has the operand and result types $`t^*` and $`r^*`.
:::

:::readable Fir.Core.decodeFloatToInt_eq (pin := Fir.Core.decodeFloatToInt) (fingerprint := "11384312465432405206")
*Theorem: a conversion to an integer decodes only from its own spelling.*
If $`\mathtt{fptosi}` or $`\mathtt{fptoui}` decodes from the attributes
$`a^*` and the types $`t^*` and $`r^*`, the op it gives is written with
that name, has the attributes $`a^*`, which are none, and has the operand
and result types $`t^*` and $`r^*`.
:::
