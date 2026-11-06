import VersoManual
import Fir.Core.Text
import Fir.Text.Decode
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the core dialect in text, which
renders `Fir.Core.Text` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The core dialect in text: readable blocks" =>

:::readable Fir.Core.Pred.name Fir.Core.Pred.all (pin := Fir.Core.Pred) (fingerprint := "13998240512404124084")
*Definition: the names of the predicates.* Each of the ten
{ref "The-fir-specification--Abstract-syntax--Core-ops"}[predicates] of
$`\mathsf{icmp}` is written as its name, as LLVM writes it:
$`\mathrm{name}(p)` is `eq`, `ne`, `slt`, `sle`, `sgt`, `sge`, `ult`,
`ule`, `ugt` or `uge`. The ten predicates are listed in that order, and the
parser looks a name up in that list to read a predicate back.
:::

:::readable Fir.Core.Op.name (pin := Fir.Core.Op) (fingerprint := "2220217634864718192")
*Definition: the name of a core op instance.* $`\mathrm{opname}(o)` is
the name of the op of $`o`, whatever its widths and attributes:
$`\mathrm{opname}(\mathsf{add}_{32}~\mathsf{nsw})` is `add`. Each of the
25 {ref "The-fir-specification--Abstract-syntax--Core-ops"}[core ops] is
written with the name it has in the op set, except the conditional branch
$`\mathsf{cond\_br}`, which the Lean spells `condBr` and the text
`cond_br`.
:::

:::readable Fir.Core.WrapFlags.attrs Fir.Core.constAttr Fir.Core.Op.attrs (pin := Fir.Core.Op) (pin := Fir.Core.WrapFlags) (fingerprint := "11960409149810052978")
*Definition: the attributes of a core op instance.* The attributes
$`\mathrm{opattrs}(o)` of a core op instance $`o` are:

$$`\begin{aligned} \mathrm{opattrs}(\mathsf{const}_N~c) &= \mathrm{constattr}_N(c) \\ \mathrm{opattrs}(\mathsf{icmp}_N~p) &= \mathrm{name}(p) \\ \mathrm{opattrs}(\mathsf{add}_N~\mathit{fl}) &= \mathrm{flags}(\mathit{fl}) \\ \mathrm{opattrs}(\mathsf{sdiv}_N~\mathit{ex}) &= \mathrm{exact}(\mathit{ex}) \\ \mathrm{opattrs}(\mathsf{call}~f : t^* \to r^*) &= \mathsf{sym}~f \\ \mathrm{opattrs}(o) &= \epsilon \quad \text{otherwise} \end{aligned}`

and the same for $`\mathsf{sub}` and $`\mathsf{mul}` as for
$`\mathsf{add}`, and for $`\mathsf{udiv}` as for $`\mathsf{sdiv}`. Here:

* $`\mathrm{constattr}_N(c)` is the word `true` or `false` when $`N = 1`, as
  $`c` is 1 or 0, and otherwise the integer that the $`N` bits of $`c` give
  when read as a two's-complement signed integer;
* $`\mathrm{flags}(\mathit{fl})` is the word `nuw` when the flag
  $`\mathsf{nuw}` is set, then the word `nsw` when $`\mathsf{nsw}` is set,
  so the flags come in this fixed order, each at most once;
* $`\mathrm{exact}(\mathit{ex})` is the word `exact` when the flag is set,
  and nothing otherwise;
* $`\mathsf{sym}~f` is the reference to the callee's symbol $`f`.

An op's widths are not among its attributes: they are the widths of the
types written where its operands and results are defined.
:::

:::readable Fir.Core.decodeWrap Fir.Core.decodeExact Fir.Core.binWidth Fir.Core.bare Fir.Core.decodeCast Fir.Core.plainBinOps Fir.Core.Op.decode (pin := Fir.Core.Op) (pin := Fir.Text.decodeOps) (fingerprint := "4111233635218291554")
*Definition: reading a core op instance back.*
$`\mathrm{decodeop}(n, a^*, t^*, r^*)` is the core op instance with the
name $`n` and the attributes $`a^*`, whose operands have the types $`t^*`
and whose results have the types $`r^*`. It uses three helpers, each
undefined outside the cases given:

* $`\mathrm{decodeflags}(a^*)` reads the flags of $`\mathsf{add}`,
  $`\mathsf{sub}` and $`\mathsf{mul}`: none from $`\epsilon`, and
  $`\mathsf{nuw}`, $`\mathsf{nsw}` or both from `nuw`, `nsw` or `nuw nsw`;
* $`\mathrm{decodeexact}(a^*)` reads the flag of $`\mathsf{sdiv}` and
  $`\mathsf{udiv}`: unset from $`\epsilon`, and set from `exact`;
* $`\mathrm{width}(t^*, r^*)` is $`A` when $`t^* = \mathsf{i}A~\mathsf{i}A`
  and $`r^* = \mathsf{i}A`: the width of an op that takes two integers of
  one type and gives one of the same type.

$`\mathrm{decodeop}` is defined only in these cases, by the name $`n`.
"Without attributes" means $`a^* = \epsilon`, and $`\mathsf{i}A`,
$`\mathsf{i}B`, $`\mathsf{i}C`, $`\mathsf{i}M`, $`\mathsf{i}N` and
$`\mathsf{i}W` are integer types.

* `const`: from `true` or `false`, no operands and the result type
  $`\mathsf{i1}`, it is $`\mathsf{const}_1~1` or $`\mathsf{const}_1~0`.
  From an integer $`v`, no operands and the result type $`\mathsf{i}W`
  with $`W \neq 1`, it is $`\mathsf{const}_W~c`, where $`c` is the
  $`W`-bit constant whose signed reading is $`v`, when there is one.
* `icmp`: from the name of a predicate $`p`, the operand types
  $`\mathsf{i}A~\mathsf{i}B` with $`A = B`, and the result type
  $`\mathsf{i1}`, it is $`\mathsf{icmp}_A~p`.
* `add`, `sub` and `mul`: when $`\mathrm{width}(t^*, r^*) = A` and
  $`\mathrm{decodeflags}(a^*) = \mathit{fl}`, it is the op at width $`A`
  with the flags $`\mathit{fl}`.
* `sdiv` and `udiv`: when $`\mathrm{width}(t^*, r^*) = A` and
  $`\mathrm{decodeexact}(a^*) = \mathit{ex}`, it is the op at width $`A`
  with the flag $`\mathit{ex}`.
* `srem`, `urem`, `and`, `or`, `xor`, `shl`, `lshr` and `ashr`: without
  attributes, when $`\mathrm{width}(t^*, r^*) = A`, it is the op at width
  $`A`.
* `select`: without attributes, from the operand types
  $`\mathsf{i1}~\mathsf{i}A~\mathsf{i}B` and the result type
  $`\mathsf{i}C`, with $`A = B = C`, it is $`\mathsf{select}_A`.
* `zext`, `sext` and `trunc`: without attributes, from one operand type
  $`\mathsf{i}M` and one result type $`\mathsf{i}N`, it is the width change
  from $`M` to $`N`.
* `freeze`: without attributes, from one operand type $`\mathsf{i}A` and
  one result type $`\mathsf{i}B` with $`A = B`, it is
  $`\mathsf{freeze}_A`.
* `poison`: without attributes, from no operands and one result type
  $`\mathsf{i}W`, it is $`\mathsf{poison}_W`.
* `br`: without attributes, operands or results, it is $`\mathsf{br}`.
* `cond_br`: without attributes, from the one operand type
  $`\mathsf{i1}` and no results, it is $`\mathsf{cond\_br}`.
* `ret`: without attributes or results, from the operand types $`t^*`, it
  is $`\mathsf{ret}~t^*`.
* `call`: from the one attribute $`\mathsf{sym}~f`, at any operand types
  $`t^*` and result types $`r^*`, it is $`\mathsf{call}~f : t^* \to r^*`.

Every other name, and every other combination of attributes and types, is
undefined, and the parser rejects the op at its name. So the core dialect
reads an op only from the one spelling that it writes, and a type mismatch,
such as `add` of an `i32` and an `i64`, does not decode. Whether the widths
are in range, and whether a width change changes the width, are left to
{ref "The-fir-specification--Validation--Core-rules"}[validation].
:::

:::readable Fir.Core.Ty.attr Fir.Core.Ty.decode (pin := Fir.Core.Ty) (pin := Fir.Core.maxWidth) (fingerprint := "2785724965273753220")
*Definition: how a core type is written, and read back.* The
{ref "The-fir-specification--Abstract-syntax--Core-types"}[integer type]
$`\mathsf{i}N` is written $`\mathrm{tyattr}(\mathsf{i}N)`, the word `i`
followed by $`N` in decimal, and $`\mathrm{tyattr}` of the pointer type is
the word `ptr`.

$`\mathrm{decodety}(a)` reads a type back. It is the pointer type when $`a`
is the word `ptr`. It is $`\mathsf{i}N` when $`a` is a word made of `i` and
the decimal digits of $`N`, with no leading zeros, and
$`N \le 16{,}777{,}215`, the widest width of the core dialect. It is
undefined otherwise, so `i032`, `u8` and `i16777216` do not decode. `i0`
decodes, and validation rejects it.
:::

:::readable Fir.Core.samples (pin := Fir.instDialectTextCoreDialect) (fingerprint := "2188211750398099125")
*Definition: the core dialect's text, and one instance of every core op.*
The functions of the blocks
above, $`\mathrm{opname}`, $`\mathrm{opattrs}`, $`\mathrm{decodeop}`,
$`\mathrm{tyattr}` and $`\mathrm{decodety}`, are the core dialect's
{ref "The-fir-specification--Text-format--Grammar"}[text], so the parser
and the printer of every dialect read and write core modules. The samples
are a list of op instances that
holds each of the 25 core ops at least once, with each of the ten
predicates, at widths from 1 to 128, with and without each flag, and
$`\mathsf{ret}` with and without operands. On every build, checks test
that each of them reads back from its own name, attributes and types, and
that misspellings such as `i032`, flags in the wrong order and `const 1`
at `i1` do not. The proof for every op instance, of every width, is in the
section {ref "The-fir-specification--Text-format--The-core-dialect___s-text-is-lawful"}[The core dialect's text is lawful].
:::
