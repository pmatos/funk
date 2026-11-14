import VersoManual
import Fir.Core.TextLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the lawful text of the core dialect,
which renders `Fir.Core.TextLaws` (ADR-2026-11-05-2012). Each block states
theorems of that module in words and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "The core dialect's text is lawful: readable blocks" =>

:::moduleDocs (fingerprint := "88123864055373757")
:::

:::readable Fir.Core.decodeWrap_attrs Fir.Core.attrs_of_decodeWrap Fir.Core.attrs_of_decodeExact (pin := Fir.Core.WrapFlags.attrs) (pin := Fir.Core.decodeWrap) (pin := Fir.Core.decodeExact) (fingerprint := "17401711866704955162")
*Theorems: flags read back from their spelling, and only from it.* With
$`\mathrm{flags}`, $`\mathrm{decodeflags}` and $`\mathrm{decodeexact}` of
the {ref "The-fir-specification--Text-format--The-core-dialect-in-text"}[previous section]:

* for all flags $`\mathit{fl}` of $`\mathsf{add}`, $`\mathsf{sub}` or
  $`\mathsf{mul}`, $`\mathrm{decodeflags}(\mathrm{flags}(\mathit{fl})) = \mathit{fl}`;
* for every list of attributes $`a^*`, if
  $`\mathrm{decodeflags}(a^*) = \mathit{fl}` then
  $`\mathrm{flags}(\mathit{fl}) = a^*`;
* for every list of attributes $`a^*`, if
  $`\mathrm{decodeexact}(a^*) = \mathit{ex}` then $`a^*` is `exact` when
  $`\mathit{ex}` is set, and $`\epsilon` when it is not.

The proofs of the laws for $`\mathsf{add}` to $`\mathsf{udiv}` use them.
:::

:::readable Fir.Core.find_pred_name Fir.Core.name_of_find_pred (pin := Fir.Core.Pred.name) (pin := Fir.Core.Pred.all) (fingerprint := "18400209700053729532")
*Theorems: a predicate is found by its name, and only by it.* For every
predicate $`p`, looking $`\mathrm{name}(p)` up in the list of the ten
predicates finds $`p`; and for every string $`s`, a predicate found by
looking $`s` up has the name $`s`. The proofs of the laws for
$`\mathsf{icmp}` use them.
:::

:::readable Fir.Core.find_fpred_name Fir.Core.name_of_find_fpred (pin := Fir.Core.FPred.name) (pin := Fir.Core.FPred.all) (fingerprint := "5854253884255476291")
*Theorems: a float predicate is found by its name, and only by it.* For
every float predicate $`p`, looking $`\mathrm{name}(p)` up in the list of
the fourteen float predicates finds $`p`; and for every string $`s`, a
float predicate found by looking $`s` up has the name $`s`. The proofs of
the laws for $`\mathsf{fcmp}` use them.
:::

:::readable Fir.Core.constAttr_of_ne_one Fir.Core.bitVec_one_cases (pin := Fir.Core.constAttr) (fingerprint := "683726526858554718")
*Theorems: the two cases of a constant.* For every width $`W \neq 1` and
every $`W`-bit value $`v`, $`\mathrm{constattr}_W(v)` is the integer $`v`
read as signed; and every 1-bit value is 1 or 0. They split the proofs for
$`\mathsf{const}` into its two spellings.
:::

:::readable Fir.Core.binWidth_eq Fir.Core.binOp_eq Fir.Core.bare_eq Fir.Core.decodeCast_eq Fir.Core.plainBinOps_lookup (pin := Fir.Core.binWidth) (pin := Fir.Core.bare) (pin := Fir.Core.decodeCast) (pin := Fir.Core.plainBinOps) (fingerprint := "7384889230442516513")
*Theorems: what each step of reading an op back accepts.* Each says that a
helper of $`\mathrm{decodeop}` succeeds only on the shape it reads:

* if $`\mathrm{width}(t^*, r^*) = A`, then $`t^* = \mathsf{i}A~\mathsf{i}A`
  and $`r^* = \mathsf{i}A`;
* an op read from its width and flags, as $`\mathsf{add}` and
  $`\mathsf{sdiv}` are, has two operands $`\mathsf{i}A`, one result
  $`\mathsf{i}A`, and flags read from its attributes;
* an op read without attributes was given none;
* a width change was read from no attributes, one operand type
  $`\mathsf{i}M` and one result type $`\mathsf{i}N`, as the width change
  from $`M` to $`N`;
* each of the eight ops $`\mathsf{srem}` to $`\mathsf{ashr}`, found by a
  name, has that name, no attributes, the operand types
  $`\mathsf{i}A~\mathsf{i}A` and the result type $`\mathsf{i}A` at every
  width $`A`.

They are the steps of the proof that an op reads back only from its own
spelling.
:::

:::readable Fir.Core.decodeFcmpWith_eq Fir.Core.decodeFcmp_eq (pin := Fir.Core.decodeFcmp) (fingerprint := "5539919355558371046")
*Theorems: a comparison of floats decodes only from its own spelling.*
If $`\mathsf{fcmp}` decodes from the attributes $`a^*` and the types
$`t^*` and $`r^*`, the op it gives has its name, the attributes $`a^*`
and the operand and result types $`t^*` and $`r^*`. Its attributes are
the words of its fast-math flags and then its predicate, and the words
that reading takes back put the attributes back together. The proof of
the next theorem uses them for this op.
:::

:::readable Fir.Core.decodePtrAdd_eq (pin := Fir.Core.decodePtrAdd) (fingerprint := "13106390997175491723")
*Theorem: a pointer offset decodes only from its own spelling.* If
$`\mathtt{ptradd}` decodes from the attributes $`a^*` and the types
$`t^*` and $`r^*`, the op it gives is written $`\mathtt{ptradd}`, has no
attributes, so $`a^*` is empty, and has the operand and result types
$`t^*` and $`r^*`: a pointer and an integer, and a pointer of the same
memory.
:::

:::readable Fir.Core.Op.decode_encode Fir.Core.Op.encode_decode (pin := Fir.Core.Op.sig) (pin := Fir.Core.Op.returnTypes) (fingerprint := "2614283961596373292")
*Theorems: every core op instance reads back from its spelling, and only
from it.* For every core op instance $`o`, valid or not:

$$`\begin{aligned} \mathrm{decodeop}(&\mathrm{opname}(o), \mathrm{opattrs}(o), \\ &\mathrm{sig}(o), \mathrm{ret}(o)) = o \end{aligned}`

where $`\mathrm{sig}(o)` and $`\mathrm{ret}(o)` are its operand and result
types, from the
{ref "The-fir-specification--Abstract-syntax--Core-signatures"}[core signatures].
And for every name $`n`, attributes $`a^*` and types $`t^*` and $`r^*`, if
$`\mathrm{decodeop}(n, a^*, t^*, r^*) = o`, then
$`\mathrm{opname}(o) = n`, $`\mathrm{opattrs}(o) = a^*`,
$`\mathrm{sig}(o) = t^*` and $`\mathrm{ret}(o) = r^*`.

These are the first two laws of a lawful text for the core dialect. The
proofs go op by op, for every width, flag, predicate, float format,
float constant, float op of arithmetic, bit cast, conversion from or to
an integer and between formats, pointer offset at every memory,
allocation of every kind, type, count and alignment, and list of types. A float constant reads back because its
signed reading names its bits exactly.
:::

:::readable Fir.Core.Op.name_isWord Fir.Core.Pred.name_isWord Fir.Core.FPred.name_isWord Fir.Core.Attr.allWritable_append Fir.Core.FastMath.attrs_writable Fir.Core.Op.attrs_writable (pin := Fir.isWord) (fingerprint := "4794657475226313482")
*Theorems: core ops are written as tokens.* For every core op instance
$`o`, $`\mathrm{opname}(o)` is a word and every attribute of
$`\mathrm{opattrs}(o)` can be written; and the name of every predicate,
an integer one or a float one, is a word. The words of the fast-math
flags can be written, and so can two lists of attributes that can, one
after the other. With the
{ref "The-fir-specification--Text-format--The-core-types-in-text-are-lawful"}[previous section],
which proves that every valid core type is written as a type, these are
the last three laws: what the core dialect writes fits the grammar.
:::

:::readable Fir.Core.lawfulDialectText Fir.Core.validIsWellFormed (pin := Fir.instLawfulDialectTextCoreDialect) (fingerprint := "2917827488444584806")
*Theorems: the core dialect's text is lawful, and every valid core module
is well formed.* The theorems above are the seven laws of a
{ref "The-fir-specification--Text-format--Grammar"}[lawful text] for the
core dialect, so its text is lawful, for all 41 ops and every type, and
the proofs about the parser use this proof for core modules. With it, every
{ref "The-fir-specification--Validation--The-general-rules"}[valid] core
module is
{ref "The-fir-specification--Text-format--Round-trips"}[well formed], so
the round trip covers every valid core module.
:::
