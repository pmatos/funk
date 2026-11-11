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

:::moduleDocs (fingerprint := "10932335744813086371")
:::

:::readable Fir.Core.Pred.name Fir.Core.Pred.all (pin := Fir.Core.Pred) (fingerprint := "13998240512404124084")
*Definition: the names of the predicates.* Each of the ten
{ref "The-fir-specification--Abstract-syntax--Core-ops"}[predicates] of
$`\mathsf{icmp}` is written as its name, as LLVM writes it:
$`\mathrm{name}(p)` is `eq`, `ne`, `slt`, `sle`, `sgt`, `sge`, `ult`,
`ule`, `ugt` or `uge`. The ten predicates are listed in that order, and the
parser looks a name up in that list to read a predicate back.
:::

:::readable Fir.Core.FPred.name Fir.Core.FPred.all (pin := Fir.Core.FPred) (fingerprint := "2855655812158596522")
*Definition: the names of the float predicates.* Each of the fourteen
{ref "The-fir-specification--Abstract-syntax--Core-ops"}[float predicates]
of $`\mathsf{fcmp}` is written as its name, as LLVM writes it: `oeq`,
`one`, `olt`, `ole`, `ogt`, `oge`, `ord`, `ueq`, `une`, `ult`, `ule`,
`ugt`, `uge` or `uno` (ADR-2026-11-11-1139). They are listed in that order,
and the parser looks a name up in that list to read a predicate back.
:::

:::readable Fir.Core.Op.name (pin := Fir.Core.Op) (fingerprint := "7904133121390987453")
*Definition: the name of a core op instance.* $`\mathrm{opname}(o)` is
the name of the op of $`o`, whatever its widths and attributes:
$`\mathrm{opname}(\mathsf{add}_{32}~\mathsf{nsw})` is `add`. Each of the
28 {ref "The-fir-specification--Abstract-syntax--Core-ops"}[core ops] is
written with the name it has in the op set, except two. The conditional
branch $`\mathsf{cond\_br}`, which the Lean spells `condBr`, is written
`cond_br`. The float constant, which the Lean spells `fconst`, is written
`const`, as an integer constant is: the type of its result tells them
apart.
:::

:::readable Fir.Core.WrapFlags.attrs Fir.Core.constAttr Fir.Core.Op.attrs (pin := Fir.Core.Op) (pin := Fir.Core.WrapFlags) (fingerprint := "12529195702843307171")
*Definition: the attributes of a core op instance.* The attributes
$`\mathrm{opattrs}(o)` of a core op instance $`o` are:

$$`\begin{aligned} \mathrm{opattrs}(\mathsf{const}_N~c) &= \mathrm{constattr}_N(c) \\ \mathrm{opattrs}(\mathsf{const}_{e,m}~v) &= \mathrm{signed}_{1+e+m}(v) \\ \mathrm{opattrs}(\mathsf{icmp}_N~p) &= \mathrm{name}(p) \\ \mathrm{opattrs}(\mathsf{fcmp}_{e,m}~p) &= \mathrm{name}(p) \\ \mathrm{opattrs}(\mathsf{add}_N~\mathit{fl}) &= \mathrm{flags}(\mathit{fl}) \\ \mathrm{opattrs}(\mathsf{sdiv}_N~\mathit{ex}) &= \mathrm{exact}(\mathit{ex}) \\ \mathrm{opattrs}(\mathsf{call}~f : t^* \to r^*) &= \mathsf{sym}~f \\ \mathrm{opattrs}(o) &= \epsilon \quad \text{otherwise} \end{aligned}`

and the same for $`\mathsf{sub}` and $`\mathsf{mul}` as for
$`\mathsf{add}`, and for $`\mathsf{udiv}` as for $`\mathsf{sdiv}`. Here:

* $`\mathrm{constattr}_N(c)` is the word `true` or `false` when $`N = 1`, as
  $`c` is 1 or 0, and otherwise the integer that the $`N` bits of $`c` give
  when read as a two's-complement signed integer;
* $`\mathrm{signed}_{1+e+m}(v)` is the integer that the $`1+e+m` bits of
  a float give when read as a two's-complement signed integer, so `f32`'s
  `1.0` is `1065353216` and its $`-0` is `-2147483648`
  (ADR-2026-11-11-1138);
* $`\mathrm{flags}(\mathit{fl})` is the word `nuw` when the flag
  $`\mathsf{nuw}` is set, then the word `nsw` when $`\mathsf{nsw}` is set,
  so the flags come in this fixed order, each at most once;
* $`\mathrm{exact}(\mathit{ex})` is the word `exact` when the flag is set,
  and nothing otherwise;
* $`\mathsf{sym}~f` is the reference to the callee's symbol $`f`.

An op's widths are not among its attributes: they are the widths of the
types written where its operands and results are defined.
:::

:::readable Fir.Core.decodeWrap Fir.Core.decodeExact Fir.Core.binWidth Fir.Core.bare Fir.Core.decodeCast Fir.Core.plainBinOps Fir.Core.Op.decode (pin := Fir.Core.Op) (pin := Fir.Text.decodeOps) (fingerprint := "6542961393573177894")
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
  $`W`-bit constant whose signed reading is $`v`, when there is one. From
  an integer $`v`, no operands and the result type
  $`\mathsf{float}\langle e,m \rangle`, it is $`\mathsf{const}_{e,m}~v'`,
  where $`v'` is the vector of $`1+e+m` bits whose signed reading is $`v`,
  when there is one.
* `icmp`: from the name of a predicate $`p`, the operand types
  $`\mathsf{i}A~\mathsf{i}B` with $`A = B`, and the result type
  $`\mathsf{i1}`, it is $`\mathsf{icmp}_A~p`.
* `fcmp`: from the name of a float predicate $`p`, the operand types
  $`\mathsf{float}\langle e,m \rangle~\mathsf{float}\langle e',m' \rangle`
  with $`e = e'` and $`m = m'`, and the result type $`\mathsf{i1}`, it is
  $`\mathsf{fcmp}_{e,m}~p`.
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
* `unreachable`: without attributes, operands or results, it is
  $`\mathsf{unreachable}`.
* `call`: from the one attribute $`\mathsf{sym}~f`, at any operand types
  $`t^*` and result types $`r^*`, it is $`\mathsf{call}~f : t^* \to r^*`.

Every other name, and every other combination of attributes and types, is
undefined, and the parser rejects the op at its name. So the core dialect
reads an op only from the one spelling that it writes, and a type mismatch,
such as `add` of an `i32` and an `i64`, does not decode. Whether the widths
are in range, and whether a width change changes the width, are left to
{ref "The-fir-specification--Validation--Core-rules"}[validation].
:::

:::readable Fir.Core.floatAlias Fir.Core.aliasFormat (fingerprint := "379769461603123496")
*Definition: the aliases of float formats.* Five float formats have a name
of their own (ADR-2026-11-09-1549), and $`\mathrm{alias}(e, m)` gives it:

* $`\mathrm{alias}(5, 10)` is `f16`, IEEE binary16;
* $`\mathrm{alias}(8, 7)` is `bf16`, bfloat16;
* $`\mathrm{alias}(8, 23)` is `f32`, IEEE binary32;
* $`\mathrm{alias}(11, 52)` is `f64`, IEEE binary64;
* $`\mathrm{alias}(15, 112)` is `f128`, IEEE binary128.

Every other format has no alias. $`\mathrm{format}(n)` reads the table the
other way: the format that the alias $`n` names, if $`n` is one.
:::

:::readable Fir.Core.Ty.attr Fir.Core.decodeFloat Fir.Core.Ty.decode (pin := Fir.Core.Ty) (pin := Fir.Core.maxWidth) (fingerprint := "6575948335157839013")
*Definition: how a core type is written, and read back.* The
{ref "The-fir-specification--Abstract-syntax--Core-types"}[integer type]
$`\mathsf{i}N` is written $`\mathrm{tyattr}(\mathsf{i}N)`, the word `i`
followed by $`N` in decimal, and $`\mathrm{tyattr}` of the pointer type is
the word `ptr`. A float type $`\mathsf{float}\langle e,m \rangle` is
written as its alias when it has one, such as `f32`, and otherwise as the
word `float` applied to $`e` and $`m`, as `float(5, 2)`
(ADR-2026-11-11-0951).

$`\mathrm{decodety}(a)` reads a type back. It is the pointer type when $`a`
is the word `ptr`. It is $`\mathsf{i}N` when $`a` is a word made of `i` and
the decimal digits of $`N`, with no leading zeros, and
$`N \le 16{,}777{,}215`, the widest width of the core dialect. It is the
float type that an alias names when $`a` is that alias. It is
$`\mathsf{float}\langle e,m \rangle` when $`a` is
$`\texttt{float}(e, m)` with $`e, m \ge 0`,
$`1 + e + m \le 16{,}777{,}215`, and no alias for the format; the Lean
calls that reading `decodeFloat`. It is undefined otherwise, so `i032`,
`u8`, `i16777216`, `f8`, `float(8, 23)`, which is written `f32`, and
`float(-1, 3)` do not decode. `i0` and `float(1, 1)` decode, and
validation rejects them.
:::

:::readable Fir.Core.samples (pin := Fir.instDialectTextCoreDialect) (fingerprint := "15386014830632868840")
*Definition: the core dialect's text, and one instance of every core op.*
The functions of the blocks
above, $`\mathrm{opname}`, $`\mathrm{opattrs}`, $`\mathrm{decodeop}`,
$`\mathrm{tyattr}` and $`\mathrm{decodety}`, are the core dialect's
{ref "The-fir-specification--Text-format--Grammar"}[text], so the parser
and the printer of every dialect read and write core modules. The samples
are a list of op instances that
holds each of the 28 core ops at least once, with each of the ten
predicates and each of the fourteen float predicates, at widths from 1 to
128, float constants at `f32`, `f64`, `f16` and
$`\mathsf{float}\langle 2,1 \rangle`, with and without each flag, and
$`\mathsf{ret}` with and without operands. On every build, checks test
that each of them reads back from its own name, attributes and types, and
that misspellings such as `i032`, `float(8, 23)`, flags in the wrong order,
`const 1` at `i1` and `const 2147483648` at `f32` do not. The proof for every op instance, of every width, is in the
section {ref "The-fir-specification--Text-format--The-core-dialect___s-text-is-lawful"}[The core dialect's text is lawful].
:::
