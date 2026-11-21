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

:::moduleDocs (fingerprint := "8876098196202086944")
:::

:::readable Fir.Core.Pred.name Fir.Core.Pred.all (pin := Fir.Core.Pred) (fingerprint := "1788544629891754135")
*Definition: the names of the predicates.* Each of the ten
{ref "The-fir-specification--Abstract-syntax--Core-ops"}[predicates] of
$`\mathsf{icmp}` is written as its name, as LLVM writes it:
$`\mathrm{name}(p)` is `eq`, `ne`, `slt`, `sle`, `sgt`, `sge`, `ult`,
`ule`, `ugt` or `uge`. The ten predicates are listed in that order, and the
parser looks a name up in that list to read a predicate back.
:::

:::readable Fir.Core.FPred.name Fir.Core.FPred.all (pin := Fir.Core.FPred) (fingerprint := "12616161590799648022")
*Definition: the names of the float predicates.* Each of the fourteen
{ref "The-fir-specification--Abstract-syntax--Core-ops"}[float predicates]
of $`\mathsf{fcmp}` is written as its name, as LLVM writes it: `oeq`,
`one`, `olt`, `ole`, `ogt`, `oge`, `ord`, `ueq`, `une`, `ult`, `ule`,
`ugt`, `uge` or `uno` (ADR-2026-11-09-1549). They are listed in that order,
and the parser looks a name up in that list to read a predicate back.
:::

:::readable Fir.Core.Op.name (pin := Fir.Core.Op) (fingerprint := "1959565420787117947")
*Definition: the name of a core op instance.* $`\mathrm{opname}(o)` is
the name of the op of $`o`, whatever its widths and attributes:
$`\mathrm{opname}(\mathsf{add}_{32}~\mathsf{nsw})` is `add`. Each of the
52 {ref "The-fir-specification--Abstract-syntax--Core-ops"}[core ops] is
written with the name it has in the op set, except fifteen. The field
address, which the Lean spells `fieldAddr`, is written `fieldaddr`. The conditional
branch $`\mathsf{cond\_br}`, which the Lean spells `condBr`, is written
`cond_br`. The float constant, which the Lean spells `fconst`, is written
`const`, as an integer constant is: the type of its result tells them
apart. $`\mathit{fbin}~o` and $`\mathit{funary}~o` are written with the
{ref "The-fir-specification--Text-format--Float-arithmetic-in-text"}[name]
of their operation $`o`, such as `fadd` or `sqrt`. Both bit casts, which
the Lean spells `toBits` and `ofBits`, are written `bitcast`: the types of
the operand and the result tell them apart. The loads and stores of a
pointer and of a float, which the Lean spells `loadPtr`, `storePtr`,
`loadFloat` and `storeFloat`, are written `load` and `store`, as those of
an integer are: the type of the value tells them apart. The copy or move,
which the Lean spells `memCopy`, is written `memcpy` for a copy and
`memmove` for a move, the fill, which the Lean spells `memSet`, is
written `memset`, and `ptrExpose` and `ptrFromInt` are written
`ptr_expose` and `ptr_from_int`.
:::

:::readable Fir.Core.WrapFlags.attrs Fir.Core.constAttr Fir.Core.Op.attrs (pin := Fir.Core.Op) (pin := Fir.Core.WrapFlags) (pin := Fir.Core.floatLit) (fingerprint := "9846150422747045543")
*Definition: the attributes of a core op instance.* The attributes
$`\mathrm{opattrs}(o)` of a core op instance $`o` are:

$$`\begin{aligned} \mathrm{opattrs}(\mathsf{const}_N~c) &= \mathrm{constattr}_N(c) \\ \mathrm{opattrs}(\mathsf{const}_{e,m}~v) &= \mathrm{floatlit}_{e,m}(v) \\ \mathrm{opattrs}(\mathsf{icmp}_N~p) &= \mathrm{name}(p) \\ \mathrm{opattrs}(\mathsf{fcmp}_{e,m}~\phi~p) &= \mathrm{fmf}(\phi)~\mathrm{name}(p) \\ \mathrm{opattrs}(\mathsf{fma}_{e,m}~\phi~r) &= \mathrm{fmf}(\phi)~\mathtt{round}(r) \\ \mathrm{opattrs}(\mathsf{sitofp}_{N,e,m}~r) = \mathrm{opattrs}(\mathsf{uitofp}_{N,e,m}~r) &= \mathtt{round}(r) \\ \mathrm{opattrs}(\mathsf{fptrunc}_{e,m,e',m'}~r) &= \mathtt{round}(r) \\ \mathrm{opattrs}(\mathit{fbin}_{e,m}~o~\phi) = \mathrm{opattrs}(\mathit{funary}_{e,m}~o~\phi) &= \mathrm{fmf}(\phi)~\mathrm{attrs}(o) \\ \mathrm{opattrs}(\mathsf{add}_N~\mathit{fl}) &= \mathrm{flags}(\mathit{fl}) \\ \mathrm{opattrs}(\mathsf{sdiv}_N~\mathit{ex}) &= \mathrm{exact}(\mathit{ex}) \\ \mathrm{opattrs}(\mathsf{call}~f : t^* \to r^*) &= \mathsf{sym}~f \\ \mathrm{opattrs}(\mathsf{fieldaddr}_N~s~j) = \mathrm{opattrs}(\mathsf{fieldaddr}_{N,W}~s~j) &= \mathsf{sym}~s~j \\ \mathrm{opattrs}(\mathsf{alloca}_N~k~t~c~a) &= \mathrm{allocaattrs}(k, t, c, a) \\ \mathrm{opattrs}(\mathsf{load}_N~o~W~a) = \mathrm{opattrs}(\mathsf{store}_N~o~W~a) &= \mathrm{loadattrs}(o, a) \\ \mathrm{opattrs}(\mathsf{load}_N~o~\mathsf{ptr}\langle M \rangle~a) = \mathrm{opattrs}(\mathsf{store}_N~o~\mathsf{ptr}\langle M \rangle~a) &= \mathrm{loadattrs}(o, a) \\ \mathrm{opattrs}(\mathsf{load}_N~o~\mathsf{float}\langle e,m \rangle~a) = \mathrm{opattrs}(\mathsf{store}_N~o~\mathsf{float}\langle e,m \rangle~a) &= \mathrm{loadattrs}(o, a) \\ \mathrm{opattrs}(\mathsf{memcpy}_N~o~W) = \mathrm{opattrs}(\mathsf{memmove}_N~o~W) = \mathrm{opattrs}(\mathsf{memset}_N~o~V~W) &= \mathrm{loadattrs}(o, \mathrm{none}) \\ \mathrm{opattrs}(o) &= \epsilon \quad \text{otherwise} \end{aligned}`

and the same for $`\mathsf{sub}` and $`\mathsf{mul}` as for
$`\mathsf{add}`, and for $`\mathsf{udiv}` as for $`\mathsf{sdiv}`. Here:

* $`\mathrm{constattr}_N(c)` is the word `true` or `false` when $`N = 1`, as
  $`c` is 1 or 0, and otherwise the integer that the $`N` bits of $`c` give
  when read as a two's-complement signed integer;
* $`\mathrm{floatlit}_{e,m}(v)` is the one
  {ref "The-fir-specification--Text-format--Float-constants-in-text"}[spelling]
  of the float $`v`: its shortest decimal when that reads back, as `1.0` or
  `-0.0` at `f32`, and otherwise its bits in hexadecimal, as `0x7fc00000`
  (ADR-2026-11-11-1438);
* $`\mathrm{flags}(\mathit{fl})` is the word `nuw` when the flag
  $`\mathsf{nuw}` is set, then the word `nsw` when $`\mathsf{nsw}` is set,
  so the flags come in this fixed order, each at most once;
* $`\mathrm{exact}(\mathit{ex})` is the word `exact` when the flag is set,
  and nothing otherwise;
* $`\mathsf{sym}~f` is the reference to the callee's symbol $`f`, and
  $`\mathsf{sym}~s~j` the reference to a layout's symbol $`s` followed by
  the integer $`j`, the number of its field;
* $`\mathrm{allocaattrs}(k, t, c, a)` is the
  {ref "The-fir-specification--Text-format--Stack-allocation-in-text"}[attributes of an allocation]:
  the word of its kind, its type as a type is written, its count when it
  is not 1, and $`\mathtt{align}(a)` when it gives an alignment;
* $`\mathrm{loadattrs}(o, a)` is the
  {ref "The-fir-specification--Text-format--Loads-in-text"}[attributes of a load]:
  the word of its ordering, and $`\mathtt{align}(a)` when it gives an
  alignment, which a store writes too;
* $`\mathtt{round}(r)` is the
  {ref "The-fir-specification--Text-format--The-rounding-mode-in-text"}[attribute of the rounding mode]
  $`r`, and $`\mathrm{attrs}(o)` is it, with the mode that $`o` carries,
  for $`\mathsf{fadd}`, $`\mathsf{fsub}`, $`\mathsf{fmul}`,
  $`\mathsf{fdiv}` and $`\mathsf{sqrt}`, and nothing for $`\mathsf{frem}`,
  $`\mathsf{fmod}`, $`\mathsf{fneg}` and $`\mathsf{fabs}`;
* $`\mathrm{fmf}(\phi)` is the words of the
  {ref "The-fir-specification--Text-format--Float-arithmetic-in-text"}[fast-math flags]
  that $`\phi` sets, in their fixed order.

An op's widths are not among its attributes: they are the widths of the
types written where its operands and results are defined.
:::

:::readable Fir.Core.decodeWrap Fir.Core.decodeExact Fir.Core.binWidth Fir.Core.bare Fir.Core.decodeCast Fir.Core.decodePtrAdd Fir.Core.plainBinOps Fir.Core.decodeFcmpWith Fir.Core.decodeFcmp Fir.Core.Op.decode (pin := Fir.Core.Op) (pin := Fir.Text.decodeOps) (pin := Fir.Core.decodeFloatLit) (fingerprint := "3519175697602407589")
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
  a float literal $`l`, no operands and the result type
  $`\mathsf{float}\langle e,m \rangle`, it is $`\mathsf{const}_{e,m}~v`,
  where $`v = \mathrm{decodelit}_{e,m}(l)`, when $`l` is the spelling of
  the bits it reads as.
* `icmp`: from the name of a predicate $`p`, the operand types
  $`\mathsf{i}A~\mathsf{i}B` with $`A = B`, and the result type
  $`\mathsf{i1}`, it is $`\mathsf{icmp}_A~p`.
* `fcmp`: from the words of flags $`\phi` and then the name of a float
  predicate $`p`, the operand types
  $`\mathsf{float}\langle e,m \rangle~\mathsf{float}\langle e',m' \rangle`
  with $`e = e'` and $`m = m'`, and the result type $`\mathsf{i1}`, it is
  $`\mathsf{fcmp}_{e,m}~\phi~p`. The Lean names this case `decodeFcmp`,
  which reads the flags, and `decodeFcmpWith`, which reads the rest.
* `fadd`, `fsub`, `fmul`, `fdiv`, `frem`, `fmod`, `fneg`, `fabs`,
  `sqrt` and `fma`: as the section on
  {ref "The-fir-specification--Text-format--Float-arithmetic-in-text"}[float arithmetic in text]
  reads them, from their attributes and their float types.
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
* `bitcast`: as the section on
  {ref "The-fir-specification--Text-format--Float-arithmetic-in-text"}[float arithmetic in text]
  reads it, from no attributes, one float type and one integer type of its
  width, in either order.
* `sitofp` and `uitofp`: as the same section reads them, from
  $`\mathtt{round}(r)` with any mode $`r`, one integer type and one float
  type.
* `fpext` and `fptrunc`: as the same section reads them, from no
  attributes for `fpext` and $`\mathtt{round}(r)` with any mode $`r` for
  `fptrunc`, and one float type to another.
* `ptradd`: without attributes, from the operand types
  $`\mathsf{ptr}\langle N \rangle` and $`\mathsf{i}W`, in that order, and
  the one result type $`\mathsf{ptr}\langle N' \rangle` with $`N = N'`, it
  is $`\mathsf{ptradd}_{N,W}`; the Lean calls that reading `decodePtrAdd`.
* `fieldaddr`: as the
  {ref "The-fir-specification--Text-format--Field-addresses-in-text"}[section on field addresses in text]
  reads it, from a layout's symbol and a field's number, a pointer and an
  optional integer index, and a pointer of the same memory.
* `fptosi` and `fptoui`: as the same section reads them, from no
  attributes, one float type and one integer type.
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
* `alloca`: from no operands and the one result type
  $`\mathsf{ptr}\langle N \rangle`, it is the allocation in memory $`N`
  that its attributes give, as the section on
  {ref "The-fir-specification--Text-format--Stack-allocation-in-text"}[stack allocation in text]
  reads them.
* `load`: from the one operand type $`\mathsf{ptr}\langle N \rangle` and
  the one result type $`\mathsf{i}W`, $`\mathsf{ptr}\langle M \rangle`
  for the load of a pointer, or $`\mathsf{float}\langle e,m \rangle` for
  the load of a float, it is the load of memory $`N` that
  its attributes give, as the section on
  {ref "The-fir-specification--Text-format--Loads-in-text"}[loads in text]
  reads them.
* `store`: from the operand types $`\mathsf{i}W`,
  $`\mathsf{ptr}\langle M \rangle` for the store of a pointer, or
  $`\mathsf{float}\langle e,m \rangle` for the store of a float, and then
  $`\mathsf{ptr}\langle N \rangle` and no result, it is the store to
  memory $`N` that its attributes give, as the section on
  {ref "The-fir-specification--Text-format--Stores-in-text"}[stores in text]
  reads them.
* `memcpy` and `memmove`: from the word of an ordering alone, the operand
  types $`\mathsf{ptr}\langle N \rangle~\mathsf{ptr}\langle N \rangle~\mathsf{i}W`
  and no result, it is the copy or the move of memory $`N`, as the section
  on {ref "The-fir-specification--Text-format--Copies-and-moves-in-text"}[copies and moves in text]
  reads them.
* `memset`: from the word of an ordering alone, the operand types
  $`\mathsf{ptr}\langle N \rangle~\mathsf{i}V~\mathsf{i}W` and no result,
  it is the fill of memory $`N`, as the section on
  {ref "The-fir-specification--Text-format--Fills-in-text"}[fills in text]
  reads it.
* `ptr_expose` and `ptr_from_int`: from no attributes, one operand of
  $`\mathsf{ptr}\langle N \rangle` and one result of $`\mathsf{i}W`, or
  the reverse, they are $`\mathsf{ptrExpose}~N~W` and
  $`\mathsf{ptrFromInt}~N~W`, as the section on
  {ref "The-fir-specification--Text-format--Pointers-as-integers-in-text"}[pointers as integers in text]
  reads them.

Every other name, and every other combination of attributes and types, is
undefined, and the parser rejects the op at its name. So the core dialect
reads an op only from the one spelling that it writes, and a type mismatch,
such as `add` of an `i32` and an `i64`, does not decode. Whether the widths
are in range, and whether a width change changes the width, are left to
{ref "The-fir-specification--Validation--Core-rules"}[validation].
:::
