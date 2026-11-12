import VersoManual
import Fir.Core.FloatOpText
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on how the float arithmetic is written,
which renders `Fir.Core.FloatOpText` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Float arithmetic in text: readable blocks" =>

:::moduleDocs (fingerprint := "11644605133510641012")
:::

:::readable Fir.Core.FBin.name Fir.Core.FUnary.name (fingerprint := "906894083440061025")
*Definition: the names of the float ops.* The ops of two operands are
written $`\mathtt{fadd}`, $`\mathtt{fsub}`, $`\mathtt{fmul}`,
$`\mathtt{fdiv}`, $`\mathtt{frem}` and $`\mathtt{fmod}`, and those of
one $`\mathtt{fneg}`, $`\mathtt{fabs}` and $`\mathtt{sqrt}`. $`\mathsf{fma}` is written $`\mathtt{fma}`.
:::

:::readable Fir.Core.roundAttr Fir.Core.FBin.attrs Fir.Core.FUnary.attrs Fir.Core.isRoundAttrs Fir.Core.FBin.attrsOk Fir.Core.FUnary.attrsOk (fingerprint := "1776735331889261039")
*Definition: the rounding attribute.* An op that rounds carries one
attribute, $`\mathtt{round(rne)}`, the word $`\mathtt{round}` applied to
the word $`\mathtt{rne}` (ADR-2026-11-11-1801). $`\mathsf{fadd}`,
$`\mathsf{fsub}`, $`\mathsf{fmul}`, $`\mathsf{fdiv}`, $`\mathsf{sqrt}` and
$`\mathsf{fma}` round; $`\mathsf{frem}`, $`\mathsf{fmod}`,
$`\mathsf{fneg}` and $`\mathsf{fabs}` do not, since their result is
exact, and carry no attribute. A list of attributes reads as rounding only
when it is exactly $`[\mathtt{round(rne)}]`, and as those of an op that
does not round only when it is empty.
:::

:::readable Fir.Core.floatOpFormat Fir.Core.decodeFBin Fir.Core.decodeFUnary Fir.Core.decodeFma (fingerprint := "1699995383106748503")
*Definition: reading a float op back.* The format of a float op of $`k`
operands is $`\mathsf{float}\langle e,m \rangle` when its operand types
are $`k` copies of that type and its one result type is that type, and it
has none otherwise. A float op decodes from its name, its attributes and
its types when its attributes read as its own and its types have a format
of its number of operands: two for $`\mathsf{fadd}`, $`\mathsf{fsub}`,
$`\mathsf{fmul}`, $`\mathsf{fdiv}`, $`\mathsf{frem}` and
$`\mathsf{fmod}`, one for $`\mathsf{fneg}`, $`\mathsf{fabs}` and
$`\mathsf{sqrt}`, and three for $`\mathsf{fma}`. So
$`\mathtt{fadd~\%a, \%b}` with no attribute, $`\mathtt{round(rtz)}`,
$`\mathtt{frem~round(rne)~\%a, \%b}`, and an $`\mathsf{f32}` added to an
$`\mathsf{f64}` do not decode.
:::

:::readable Fir.Core.eq_of_isRoundAttrs Fir.Core.FBin.attrs_of_attrsOk Fir.Core.FUnary.attrs_of_attrsOk Fir.Core.floatOpFormat_eq Fir.Core.floatOpFormat_replicate (fingerprint := "11995233360236892250")
*Theorems: what the round trip needs.* Attributes that read as rounding
are $`[\mathtt{round(rne)}]`, and attributes that read as those of an op
of two operands or of one are its own. A format is found only at $`k` operands and one
result of it, and it is found there. So each float op reads back from how
it is written, and from nothing else.
:::
