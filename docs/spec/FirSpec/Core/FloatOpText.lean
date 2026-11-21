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

:::moduleDocs (fingerprint := "15480533653474075516")
:::

:::readable Fir.Core.FBin.name Fir.Core.FUnary.name (fingerprint := "8863009115999354928")
*Definition: the names of the float ops.* The ops of two operands are
written $`\mathtt{fadd}`, $`\mathtt{fsub}`, $`\mathtt{fmul}`,
$`\mathtt{fdiv}`, $`\mathtt{frem}` and $`\mathtt{fmod}`, and those of
one $`\mathtt{fneg}`, $`\mathtt{fabs}` and $`\mathtt{sqrt}`. $`\mathsf{fma}` is written $`\mathtt{fma}`.
:::

:::readable Fir.Core.FastMath.attrs Fir.Core.takeWord Fir.Core.splitFlags Fir.Core.flagFree (fingerprint := "5441382323938434904")
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

:::readable Fir.Core.FBin.attrs Fir.Core.FUnary.attrs Fir.Core.FBin.read Fir.Core.FUnary.read (fingerprint := "12533988152709561935")
*Definition: the rounding attribute.* An op that rounds carries one
attribute, its mode $`\mathtt{round}(r)`
({ref "The-fir-specification--Text-format--The-rounding-mode-in-text"}[the rounding mode in text];
ADR-2026-11-11-1801). $`\mathsf{fadd}`,
$`\mathsf{fsub}`, $`\mathsf{fmul}`, $`\mathsf{fdiv}`, $`\mathsf{sqrt}` and
$`\mathsf{fma}` round; $`\mathsf{frem}`, $`\mathsf{fmod}`,
$`\mathsf{fneg}` and $`\mathsf{fabs}` do not, since their result is
exact, and carry no attribute. Reading an op of two operands or of one by
its name takes the attributes after the flags: for an op that rounds they
must be exactly $`[\mathtt{round}(r)]`, with $`r` any of the five modes,
which the op then carries; for one that does not round they must be
empty. Any mode reads, and validation accepts only $`\mathtt{rne}`.
:::

:::readable Fir.Core.floatOpFormat Fir.Core.decodeFBin Fir.Core.decodeFUnary Fir.Core.decodeFma (fingerprint := "5980757695624137591")
*Definition: reading a float op back.* The format of a float op of $`k`
operands is $`\mathsf{float}\langle e,m \rangle` when its operand types
are $`k` copies of that type and its one result type is that type, and it
has none otherwise. A float op decodes from its name, its attributes and
its types when its attributes read as its own and its types have a format
of its number of operands: two for $`\mathsf{fadd}`, $`\mathsf{fsub}`,
$`\mathsf{fmul}`, $`\mathsf{fdiv}`, $`\mathsf{frem}` and
$`\mathsf{fmod}`, one for $`\mathsf{fneg}`, $`\mathsf{fabs}` and
$`\mathsf{sqrt}`, and three for $`\mathsf{fma}`. So
$`\mathtt{fadd~\%a, \%b}` with no attribute, $`\mathtt{round(up)}`,
$`\mathtt{frem~round(rne)~\%a, \%b}`, and an $`\mathsf{f32}` added to an
$`\mathsf{f64}` do not decode, while $`\mathtt{fadd~round(rtz)~\%a, \%b}`
decodes, with the mode $`\mathtt{rtz}`, for validation to reject. The flags are read first, and the
attributes after them must be the op's own, so
$`\mathtt{fadd~round(rne)~nnan}` does not decode either.
:::

:::readable Fir.Core.takeWord_spec Fir.Core.splitFlags_spec Fir.Core.takeWord_free Fir.Core.splitFlags_attrs (fingerprint := "2186844213968338269")
*Theorems: the flags read back.* The flags read from attributes, written
back before the attributes after them, are those attributes. And the
words of flags $`\phi`, before attributes free of flags, read back as
$`\phi` and those attributes: none of the op's own attributes, a
predicate or $`\mathtt{round}(r)`, is a flag's word.
:::

:::readable Fir.Core.decodeBitcast (pin := Fir.Core.floatWidth) (fingerprint := "15077216834255652181")
*Definition: reading a bit cast back.* $`\mathtt{bitcast}` decodes from
no attributes, one operand type and one result type, one of them
$`\mathsf{float}\langle e,m \rangle` and the other $`\mathsf{i}N` with
$`N = 1+e+m`. From the float to the integer it is
$`\mathsf{bitcast}_{e,m}^{\to \mathsf{i}}`, and from the integer to the
float $`\mathsf{bitcast}_{e,m}^{\mathsf{i} \to}`. So
$`\mathtt{bitcast}` from an $`\mathsf{f32}` to an $`\mathsf{i64}`, between
two floats or two integers, or with $`\mathtt{round(rne)}` does not
decode.
:::

:::readable Fir.Core.decodeIntToFloat (pin := Fir.Core.decodeRound) (fingerprint := "13979528417513465885")
*Definition: reading a conversion from an integer back.*
$`\mathtt{sitofp}` and $`\mathtt{uitofp}` decode from the attributes
$`[\mathtt{round}(r)]`, one operand type $`\mathsf{i}N` and one result
type $`\mathsf{float}\langle e,m \rangle`, for any mode $`r`, $`N`, $`e`
and $`m`, as $`\mathsf{sitofp}_{N,e,m}~r` and $`\mathsf{uitofp}_{N,e,m}~r`.
So a conversion with no attribute or with a word that is no mode, from a
float or to an integer, does not decode; one with $`\mathtt{round(rtz)}`
decodes, for validation to reject.
:::

:::readable Fir.Core.decodeFpext Fir.Core.decodeFptrunc (pin := Fir.Core.decodeRound) (fingerprint := "5011438224362355744")
*Definition: reading a conversion between formats back.*
$`\mathtt{fpext}` decodes from no attributes, and $`\mathtt{fptrunc}`
from the attributes $`[\mathtt{round}(r)]`, for any mode $`r`, each with
one operand type $`\mathsf{float}\langle e,m \rangle` and one result type
$`\mathsf{float}\langle e',m' \rangle`, for any two formats, as
$`\mathsf{fpext}_{e,m,e',m'}` and $`\mathsf{fptrunc}_{e,m,e',m'}~r`. So
$`\mathtt{fpext}` with $`\mathtt{round(rne)}`, $`\mathtt{fptrunc}`
without a mode, or either from or to an integer does not decode. Which pairs
of formats each takes is a
{ref "The-fir-specification--Validation--Core-rules"}[core rule] of
validation.
:::

:::readable Fir.Core.decodeFloatToInt (fingerprint := "5773104167111137232")
*Definition: reading a conversion to an integer back.*
$`\mathtt{fptosi}` and $`\mathtt{fptoui}` decode from no attributes, one
operand type $`\mathsf{float}\langle e,m \rangle` and one result type
$`\mathsf{i}N`, for any $`e`, $`m` and $`N`, as
$`\mathsf{fptosi}_{e,m,N}` and $`\mathsf{fptoui}_{e,m,N}`. So a
conversion with $`\mathtt{round(rne)}`, $`\mathtt{round(rtz)}` or any
other attribute, from an integer or to a float, does not decode: it
truncates, and has no rounding mode.
:::

:::readable Fir.Core.FBin.read_eq Fir.Core.FBin.read_name_attrs Fir.Core.FUnary.read_eq Fir.Core.FUnary.read_name_attrs Fir.Core.floatOpFormat_eq Fir.Core.floatOpFormat_replicate (fingerprint := "5048987812252335490")
*Theorems: what the round trip needs.* An op of two operands or of one
read from a name and attributes has that name and those attributes, and
each such op reads back from its own name and attributes, whatever its
mode. A format is found only at $`k` operands and one
result of it, and it is found there. So each float op reads back from how
it is written, and from nothing else.
:::
