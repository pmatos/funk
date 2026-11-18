import VersoManual
import Fir.Core.Validation
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the core rules, which renders
`Fir.Core.Validation` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Core rules: readable blocks" =>

:::moduleDocs (fingerprint := "13316978674594412478")
:::

:::readable Fir.Core.Ty.Valid Fir.Core.Ty.memory (pin := Fir.Core.maxWidth) (pin := Fir.Core.floatWidth) (fingerprint := "744407091263889301")
*Definition: valid core types.* A
{ref "The-fir-specification--Abstract-syntax--Core-types"}[core type] is
valid when it is an integer type $`\mathsf{i}N` whose width $`N` is at
least 1 and at most $`2^{24} - 1 = 16{,}777{,}215`, MLIR's limit, or a
float type $`\mathsf{float}\langle e,m \rangle` with at least 2 exponent
bits, at least 1 mantissa bit, and at most $`2^{24} - 1` bits in all, or
a pointer type $`\mathsf{ptr}\langle N \rangle` whose memory $`N` is at
most $`2^{24} - 1`.

$$`\frac{1 \le N \le 2^{24} - 1}{\vdash \mathsf{i}N~\text{valid}}`

$$`\frac{e \ge 2 \qquad m \ge 1 \qquad 1 + e + m \le 2^{24} - 1}{\vdash \mathsf{float}\langle e,m \rangle~\text{valid}}`

$$`\frac{N \le 2^{24} - 1}{\vdash \mathsf{ptr}\langle N \rangle~\text{valid}}`

The general rules write $`\vdash_d` for the rules of the dialect $`d`; for
the core dialect this section drops the subscript. $`\mathsf{i0}` is never
valid, since it would hold no bits. A float format needs 2 exponent bits
and 1 mantissa bit to hold zeros, subnormal and normal numbers,
infinities and NaNs: these are the smallest widths of Lean's float model,
on which the float ops are defined, and the core accepts every format of
that model (ADR-2026-11-09-1549). $`\mathsf{float}\langle 2,1 \rangle`
is the smallest valid format. Whether the module has the memory $`N` of a
pointer type is the rule of the module's
{ref "The-fir-specification--Validation--The-data-layout___s-rules"}[data layout],
which reads the memory that the type names: $`\mathrm{memory}(\mathsf{ptr}\langle N \rangle) = N`,
and an integer or a float type names none. Every module has the default
memory, so $`\mathsf{ptr}`, which is $`\mathsf{ptr}\langle 0 \rangle`, is
in every module, and $`\mathsf{ptr}\langle N \rangle` with $`N \ge 1` is in
a module whose layout declares memory $`N` (ADR-2026-11-12-1821).
:::

:::readable Fir.Core.Op.symbolRefs (fingerprint := "9169673307230543629")
*Definition: the symbols a core op refers to.* $`\mathsf{call}~f : t^* \to r^*`
refers to the symbol $`f` of its callee: its list of symbols is the
one-element sequence $`(f)`. No other core op refers to a symbol.

$$`\mathrm{refs}(\mathsf{call}~f : t^* \to r^*) = (f)`

$$`\mathrm{refs}(\mathit{op}) = \epsilon \ \text{ for every other op}`

The general rules check that $`f` names a function of the module.
:::

:::readable Fir.Core.Ty.IsElem (fingerprint := "15743480132225506412")
*Definition: the element types of a work-group allocation.* An integer
type $`\mathsf{i}W` and a pointer type $`\mathsf{ptr}\langle M \rangle` are
elements, and a float type is not:

$$`\mathrm{elem}(\mathsf{i}W) \qquad \mathrm{elem}(\mathsf{ptr}\langle M \rangle) \qquad \neg\,\mathrm{elem}(\mathsf{float}\langle e,m \rangle)`

`gpu.work_group_alloca` allocates elements only. The core's
$`\mathsf{alloca}` allocates values of every valid type, a float's
included, since #264 gives floats their loads and stores.
:::

:::readable Fir.Core.Op.attrTypes (fingerprint := "14541402550165652625")
*Definition: the types a core op carries.* $`\mathsf{alloca}_N~k~t~c~a`
carries the type $`t` that it allocates values of in its attributes, when
$`t` is valid:

$$`\mathrm{optypes}(\mathsf{alloca}_N~k~t~c~a) = \begin{cases} (t) & \vdash t~\text{valid} \\ \epsilon & \text{otherwise} \end{cases} \qquad \mathrm{optypes}(\mathit{op}) = \epsilon \ \text{ for every other op}`

So the data layout declares the memory $`M` of an
$`\mathsf{alloca}~\mathsf{stack}~\mathsf{ptr}\langle M \rangle`, as it
declares that of every type a function states. A type that is not valid,
such as a pointer of a memory above the bound, breaks the op's own rule and
names no memory to check, as no type written for a value can. No other
core op carries a type of its own: $`\mathsf{call}`'s are its callee's, and
$`\mathsf{ret}`'s the function's results.
:::

:::readable Fir.Core.FBin.mode Fir.Core.FUnary.mode Fir.Core.Op.Valid (pin := Fir.isPowerOfTwo) (pin := Fir.MemLayout.limit) (pin := Fir.MemLayout.ValidAlign) (fingerprint := "7601155670973002638")
*Definition: the core rules of an op.* Beyond its signature, which the
{ref "The-fir-specification--Validation--The-general-rules"}[general rules]
check, a core op obeys these rules in its op context $`C`:

$$`\frac{t^* = \mathrm{results}_C}{C \vdash \mathsf{ret}~t^*~\text{valid}}`

$$`\frac{\mathrm{symtab}_C(f) = (t^* \to r^*)}{C \vdash \mathsf{call}~f : t^* \to r^*~\text{valid}}`

$$`\frac{M < N}{C \vdash \mathsf{zext}_{M \to N}~\text{valid}}`

$$`\frac{M < N}{C \vdash \mathsf{sext}_{M \to N}~\text{valid}}`

$$`\frac{N < M}{C \vdash \mathsf{trunc}_{M \to N}~\text{valid}}`

$$`\frac{e \le e' \qquad m \le m' \qquad (e, m) \ne (e', m')}{C \vdash \mathsf{fpext}_{e,m,e',m'}~\text{valid}}`

$$`\frac{r = \mathsf{rne} \qquad e' < e \ \text{ or } \ m' < m}{C \vdash \mathsf{fptrunc}_{e,m,e',m'}~r~\text{valid}}`

$$`\frac{r = \mathsf{rne}}{C \vdash \mathsf{sitofp}_{N,e,m}~r~\text{valid}} \qquad \frac{r = \mathsf{rne}}{C \vdash \mathsf{uitofp}_{N,e,m}~r~\text{valid}}`

$$`\frac{\phi \text{ sets neither } \mathsf{contract} \text{ nor } \mathsf{reassoc}}{C \vdash \mathsf{fcmp}_{e,m}~\phi~p~\text{valid}}`

$$`\frac{\phi \text{ sets neither } \mathsf{contract} \text{ nor } \mathsf{reassoc} \qquad \mathrm{mode}(o) \text{ is none or } \mathsf{rne}}{C \vdash \mathit{op}_{e,m}~o~\phi~\text{valid}} \quad \text{for } \mathit{op} \in \{\mathit{fbin}, \mathit{funary}\}`

$$`\frac{\phi \text{ sets neither } \mathsf{contract} \text{ nor } \mathsf{reassoc} \qquad r = \mathsf{rne}}{C \vdash \mathsf{fma}_{e,m}~\phi~r~\text{valid}}`

The reserved words $`\mathsf{contract}` and $`\mathsf{reassoc}` are
permissions for passes that M2's optimizer decides, not meanings of an
op, so a float op that carries either is not valid (ADR-2026-11-09-1549).
An op that rounds rounds with the mode $`\mathsf{rne}`, the one M1
accepts: the other
{ref "The-fir-specification--Abstract-syntax--Rounding-modes"}[modes] are
hooks in the format for a later milestone (ADR-2026-11-11-1801; the
human's ruling of 2026-11-15 on #229). $`\mathrm{mode}(o)` is the mode of
$`\mathsf{fadd}`, $`\mathsf{fsub}`, $`\mathsf{fmul}`, $`\mathsf{fdiv}` and
$`\mathsf{sqrt}`, and none for $`\mathsf{frem}`, $`\mathsf{fmod}`,
$`\mathsf{fneg}` and $`\mathsf{fabs}`, which do not round.

$$`\frac{k = \mathsf{stack} \qquad c \ge 1 \qquad a \text{ is none or a valid alignment} \qquad \vdash t~\text{valid}}{C \vdash \mathsf{alloca}_{N}~k~t~c~a~\text{valid}}`

$$`\frac{o = \mathsf{nonatomic} \qquad a \text{ is none or a valid alignment}}{C \vdash \mathsf{load}_{N}~o~W~a~\text{valid}}`

$$`\frac{o = \mathsf{nonatomic} \qquad a \text{ is none or a valid alignment}}{C \vdash \mathsf{store}_{N}~o~W~a~\text{valid}}`

and the same for the load and store of a pointer,
$`\mathsf{load}_{N}~o~\mathsf{ptr}\langle M \rangle~a` and
$`\mathsf{store}_{N}~o~\mathsf{ptr}\langle M \rangle~a`, and of a float,
$`\mathsf{load}_{N}~o~\mathsf{float}\langle e,m \rangle~a` and
$`\mathsf{store}_{N}~o~\mathsf{float}\langle e,m \rangle~a`.

$$`\frac{\mathit{op} \text{ is another core op}}{C \vdash \mathit{op}~\text{valid}}`

Here $`\mathrm{results}_C` is the result types of the function that holds
the op, and $`\mathrm{symtab}_C` the module's
{ref "The-fir-specification--Validation--Scope-and-symbols"}[symbol table].

* $`\mathsf{ret}` returns values of the function's result types, any number
  of them.
* $`\mathsf{call}` passes and receives the types that the symbol table gives
  its callee, any number of each.
* $`\mathsf{zext}` and $`\mathsf{sext}` strictly widen and
  $`\mathsf{trunc}` strictly narrows. A width change to the same width is
  not an op: the value itself is.
* $`\mathsf{fpext}` converts to a format that holds every value of the
  source, with at least as many exponent bits and as many mantissa bits,
  so it never rounds; $`\mathsf{fptrunc}` rounds into a format that cannot
  hold every value of the source, with fewer exponent bits or fewer
  mantissa bits. So every ordered pair of two formats takes exactly one of
  the two, as the human ruled on 2026-11-12 (#354): $`\mathsf{f32}` to
  $`\mathsf{f64}` takes $`\mathsf{fpext}`, and $`\mathsf{f64}` to
  $`\mathsf{f32}` takes $`\mathsf{fptrunc}`, and so do $`\mathsf{bf16}` to
  $`\mathsf{f16}` and $`\mathsf{f16}` to $`\mathsf{bf16}`, since
  $`\mathsf{f16}` has fewer exponent bits than $`\mathsf{bf16}` and more
  mantissa bits. A conversion to the same format is not an op.
* $`\mathsf{alloca}` allocates on the stack, the one kind M1 accepts:
  $`\mathsf{global}` and $`\mathsf{heap}` are hooks in the format, which a
  later milestone may accept (ADR-2026-11-09-1542). It allocates at least
  one value, aligned, when it gives an alignment, to a
  {ref "The-fir-specification--Validation--The-data-layout___s-rules"}[valid alignment]:
  a power of two of units no larger than $`2^{24} - 1`, the data layout's
  rule for its own alignments, as the human ruled on 2026-11-14 (#382), so
  $`2^{23}` is the largest alignment it gives. One that gives none takes its
  type's natural alignment, which the bound does not cover, as the human
  ruled on 2026-11-14 (#385). Its type is a valid type: an integer type
  $`\mathsf{i}W`, a pointer type $`\mathsf{ptr}\langle M \rangle`, as
  stage 4d-2b of #231 adds pointer loads and stores (the human's ruling of
  2026-11-14 on #382), or a float type
  $`\mathsf{float}\langle e,m \rangle`, as #264 adds float loads and
  stores (the human's ruling of 2026-11-15 on #397). Its count has no bound: an allocation larger
  than a machine holds is a resource error at run time, as a deep
  recursion is.
  Its result's type $`\mathsf{ptr}\langle N \rangle` names its memory,
  which the module's data layout must declare, as for every pointer type
  (ADR-2026-11-14-0915), and so does a pointer type that it allocates
  values of, which it carries in its attributes ($`\mathrm{optypes}`). So
  $`\mathsf{alloca}~\mathsf{stack}~\mathsf{i32}~4`,
  $`\mathsf{alloca}~\mathsf{stack}~\mathsf{i8}~\mathsf{align}(2^{23})`,
  $`\mathsf{alloca}~\mathsf{stack}~\mathsf{ptr}~2` and
  $`\mathsf{alloca}~\mathsf{stack}~\mathsf{f32}` are valid, and
  $`\mathsf{alloca}~\mathsf{heap}~\mathsf{i32}`,
  $`\mathsf{alloca}~\mathsf{stack}~\mathsf{i32}~0`,
  $`\mathsf{alloca}~\mathsf{stack}~\mathsf{i8}~\mathsf{align}(3)`,
  $`\mathsf{alloca}~\mathsf{stack}~\mathsf{i8}~\mathsf{align}(2^{24})` and
  $`\mathsf{alloca}~\mathsf{stack}~\mathsf{float}(1, 23)` are not.
* $`\mathsf{load}` has the ordering $`\mathsf{nonatomic}`, the one M1
  accepts: the atomic orderings are hooks in the format for a concurrency
  model (ADR-2026-11-09-1542). An alignment that it gives is a valid
  alignment, as $`\mathsf{alloca}`'s is; one that it does not give is the
  natural alignment of $`\mathsf{i}W` in its memory. Its result type
  $`\mathsf{i}W` and its operand type $`\mathsf{ptr}\langle N \rangle`
  are checked as every type is: the width is valid, and the module's data
  layout declares memory $`N`. So
  $`\mathsf{load}~\mathsf{nonatomic}~\mathsf{align}(4)` is valid, and
  $`\mathsf{load}~\mathsf{seq\_cst}` and
  $`\mathsf{load}~\mathsf{nonatomic}~\mathsf{align}(3)` are not.
* $`\mathsf{store}` has the rules of $`\mathsf{load}`: the ordering
  $`\mathsf{nonatomic}`, and a valid alignment when it gives one. Its
  operand types, the value's $`\mathsf{i}W` and then the pointer's
  $`\mathsf{ptr}\langle N \rangle`, are checked as every type is. So
  $`\mathsf{store}~\mathsf{nonatomic}` is valid, and
  $`\mathsf{store}~\mathsf{release}` is not.
* The load and store of a pointer have the rules of $`\mathsf{load}` and
  $`\mathsf{store}`. The pointer type $`\mathsf{ptr}\langle M \rangle`
  that they load or store is a value's type, so the data layout must
  declare memory $`M`, as for every type.
* The load and store of a float have the rules of $`\mathsf{load}` and
  $`\mathsf{store}` too. With no alignment, the access is aligned to the
  natural alignment of the float's size in its memory, that of
  $`\mathsf{i}(1+e+m)`. The float type is a value's type, checked as every
  type is: a valid format.

Every other op has no rule beyond its signature. These definitions
are what the core dialect
{ref "The-fir-specification--Validation--Scope-and-symbols"}[adds to validation].
:::
