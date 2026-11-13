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

:::moduleDocs (fingerprint := "5740043468119939785")
:::

:::readable Fir.Core.decodeFBin_eq Fir.Core.decodeFUnary_eq Fir.Core.decodeFma_eq (pin := Fir.Core.decodeFBin) (pin := Fir.Core.decodeFUnary) (pin := Fir.Core.decodeFma) (fingerprint := "3122977627371042591")
*Theorems: a float op of arithmetic decodes only from its own spelling.*
If $`\mathsf{fadd}`, $`\mathsf{fsub}`, $`\mathsf{fmul}`,
$`\mathsf{fdiv}`, $`\mathsf{frem}` or $`\mathsf{fmod}` decodes from the attributes $`a^*` and the types $`t^*`
and $`r^*`, as the section on
{ref "The-fir-specification--Text-format--Float-arithmetic-in-text"}[float arithmetic in text]
reads it, the op it gives has its name, the attributes $`a^*` and the
operand and result types $`t^*` and $`r^*`; and the same holds of
$`\mathsf{fneg}`, $`\mathsf{fabs}`, $`\mathsf{sqrt}` and $`\mathsf{fma}`.
The proof that every core op reads back, in the next section, uses them
for these ops.
:::

:::readable Fir.Core.decodeBitcast_eq (pin := Fir.Core.decodeBitcast) (fingerprint := "3952252289645912107")
*Theorem: a bit cast decodes only from its own spelling.* If
$`\mathtt{bitcast}` decodes from the attributes $`a^*` and the types
$`t^*` and $`r^*`, the op it gives, in either direction, is written
$`\mathtt{bitcast}`, has no attributes, so $`a^*` is empty, and has the
operand and result types $`t^*` and $`r^*`.
:::

:::readable Fir.Core.decodeIntToFloat_eq (pin := Fir.Core.decodeIntToFloat) (fingerprint := "18079157018789560655")
*Theorem: a conversion from an integer decodes only from its own
spelling.* If $`\mathtt{sitofp}` or $`\mathtt{uitofp}` decodes from the
attributes $`a^*` and the types $`t^*` and $`r^*`, the op it gives is
written with that name, has the attributes $`a^*`, which are
$`[\mathtt{round(rne)}]`, and has the operand and result types $`t^*` and
$`r^*`.
:::

:::readable Fir.Core.decodeFpext_eq Fir.Core.decodeFptrunc_eq (pin := Fir.Core.decodeFpext) (pin := Fir.Core.decodeFptrunc) (fingerprint := "18338062105868789928")
*Theorems: a conversion between formats decodes only from its own
spelling.* If $`\mathtt{fpext}` or $`\mathtt{fptrunc}` decodes from the
attributes $`a^*` and the types $`t^*` and $`r^*`, the op it gives is
written with that name, has the attributes $`a^*`, which are none for
$`\mathtt{fpext}` and $`[\mathtt{round(rne)}]` for $`\mathtt{fptrunc}`,
and has the operand and result types $`t^*` and $`r^*`.
:::

:::readable Fir.Core.decodeFloatToInt_eq (pin := Fir.Core.decodeFloatToInt) (fingerprint := "10685283668543585865")
*Theorem: a conversion to an integer decodes only from its own spelling.*
If $`\mathtt{fptosi}` or $`\mathtt{fptoui}` decodes from the attributes
$`a^*` and the types $`t^*` and $`r^*`, the op it gives is written with
that name, has the attributes $`a^*`, which are none, and has the operand
and result types $`t^*` and $`r^*`.
:::
