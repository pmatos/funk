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

:::moduleDocs (fingerprint := "6118023958744219030")
:::

:::readable Fir.Core.FBin.name Fir.Core.FUnary.name (fingerprint := "13778199030025655354")
*Definition: the names of the float ops.* The ops of two operands are
written $`\mathtt{fadd}`, $`\mathtt{fsub}`, $`\mathtt{fmul}` and
$`\mathtt{fdiv}`, and those of one $`\mathtt{fneg}`, $`\mathtt{fabs}` and
$`\mathtt{sqrt}`. $`\mathsf{fma}` is written $`\mathtt{fma}`.
:::

:::readable Fir.Core.FastMath.attrs Fir.Core.takeWord Fir.Core.splitFlags Fir.Core.flagFree (fingerprint := "12119595488592313051")
*Definition: the flags in text.* The fast-math flags $`\phi` are written
as words, one for each flag set, in the fixed order $`\mathtt{nnan}`,
$`\mathtt{ninf}`, $`\mathtt{nsz}`, $`\mathtt{contract}`,
$`\mathtt{reassoc}`, before the op's other attributes:
$`\mathtt{fadd~nnan~nsz~round(rne)~\%a, \%b}` and
$`\mathtt{fcmp~ninf~olt~\%a, \%b}`.

Reading takes the words back from the front of the attributes in that
order: each is taken when it is the next attribute, and the attributes
after the last word taken are the op's others. So a flag out of order, or
written twice, is left among the others, and the op does not decode: each
op has one spelling. Attributes are _free of flags_ when they do not start
with one of the five words.
:::

:::readable Fir.Core.roundAttr Fir.Core.FUnary.attrs Fir.Core.isRoundAttrs Fir.Core.FUnary.attrsOk (fingerprint := "15382503822467167193")
*Definition: the rounding attribute.* An op that rounds carries one
attribute, $`\mathtt{round(rne)}`, the word $`\mathtt{round}` applied to
the word $`\mathtt{rne}` (ADR-2026-11-11-1801). $`\mathsf{fadd}`,
$`\mathsf{fsub}`, $`\mathsf{fmul}`, $`\mathsf{fdiv}`, $`\mathsf{sqrt}` and
$`\mathsf{fma}` round; $`\mathsf{fneg}` and $`\mathsf{fabs}` do not, and
carry no attribute. A list of attributes reads as rounding only when it is
exactly $`[\mathtt{round(rne)}]`, and as those of $`\mathsf{fneg}` or
$`\mathsf{fabs}` only when it is empty.
:::

:::readable Fir.Core.floatOpFormat Fir.Core.decodeFBin Fir.Core.decodeFUnary Fir.Core.decodeFma (fingerprint := "13176774849152649178")
*Definition: reading a float op back.* The format of a float op of $`k`
operands is $`\mathsf{float}\langle e,m \rangle` when its operand types
are $`k` copies of that type and its one result type is that type, and it
has none otherwise. A float op decodes from its name, its attributes and
its types when its attributes read as its own and its types have a format
of its number of operands: two for $`\mathsf{fadd}`, $`\mathsf{fsub}`,
$`\mathsf{fmul}` and $`\mathsf{fdiv}`, one for $`\mathsf{fneg}`,
$`\mathsf{fabs}` and $`\mathsf{sqrt}`, and three for $`\mathsf{fma}`. So
$`\mathtt{fadd~\%a, \%b}` with no attribute, $`\mathtt{round(rtz)}`, and an
$`\mathsf{f32}` added to an $`\mathsf{f64}` do not decode. The flags are
read first, and the attributes after them must be the op's own, so
$`\mathtt{fadd~round(rne)~nnan}` does not decode either.
:::

:::readable Fir.Core.takeWord_spec Fir.Core.splitFlags_spec Fir.Core.takeWord_free Fir.Core.splitFlags_attrs (fingerprint := "2186844213968338269")
*Theorems: the flags read back.* The flags read from attributes, written
back before the attributes after them, are those attributes. And the
words of flags $`\phi`, before attributes free of flags, read back as
$`\phi` and those attributes: none of the op's own attributes, a
predicate or $`\mathtt{round(rne)}`, is a flag's word.
:::

:::readable Fir.Core.eq_of_isRoundAttrs Fir.Core.FUnary.attrs_of_attrsOk Fir.Core.floatOpFormat_eq Fir.Core.floatOpFormat_replicate (fingerprint := "1937090943893134182")
*Theorems: what the round trip needs.* Attributes that read as rounding
are $`[\mathtt{round(rne)}]`, and attributes that read as those of an op
of one operand are its own. A format is found only at $`k` operands and one
result of it, and it is found there. So each float op reads back from how
it is written, and from nothing else.
:::
