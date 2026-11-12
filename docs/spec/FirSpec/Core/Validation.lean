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

:::moduleDocs (fingerprint := "2653196257881618060")
:::

:::readable Fir.Core.Ty.Valid (pin := Fir.Core.maxWidth) (pin := Fir.Core.floatWidth) (fingerprint := "5367422729387808105")
*Definition: valid core types.* A
{ref "The-fir-specification--Abstract-syntax--Core-types"}[core type] is
valid when it is an integer type $`\mathsf{i}N` whose width $`N` is at
least 1 and at most $`2^{24} - 1 = 16{,}777{,}215`, MLIR's limit, or a
float type $`\mathsf{float}\langle e,m \rangle` with at least 2 exponent
bits, at least 1 mantissa bit, and at most $`2^{24} - 1` bits in all, or
a pointer type $`\mathsf{ptr}\langle N \rangle` of a memory $`N` that the
module has.

$$`\frac{1 \le N \le 2^{24} - 1}{\vdash \mathsf{i}N~\text{valid}}`

$$`\frac{e \ge 2 \qquad m \ge 1 \qquad 1 + e + m \le 2^{24} - 1}{\vdash \mathsf{float}\langle e,m \rangle~\text{valid}}`

$$`\frac{}{\vdash \mathsf{ptr}\langle 0 \rangle~\text{valid}}`

The general rules write $`\vdash_d` for the rules of the dialect $`d`; for
the core dialect this section drops the subscript. $`\mathsf{i0}` is never
valid, since it would hold no bits. A float format needs 2 exponent bits
and 1 mantissa bit to hold zeros, subnormal and normal numbers,
infinities and NaNs: these are the smallest widths of Lean's float model,
on which the float ops are defined, and the core accepts every format of
that model (ADR-2026-11-09-1549). $`\mathsf{float}\langle 2,1 \rangle`
is the smallest valid format. Every module has the default memory, so
$`\mathsf{ptr}`, which is $`\mathsf{ptr}\langle 0 \rangle`, is valid. No
module has another memory until the data layout declares memories (#231),
so no rule concludes $`\vdash \mathsf{ptr}\langle N \rangle~\text{valid}`
for $`N \ge 1`.
:::

:::readable Fir.Core.Op.symbolRefs (fingerprint := "14722312557016654371")
*Definition: the symbols a core op refers to.* $`\mathsf{call}~f : t^* \to r^*`
refers to the symbol $`f` of its callee: its list of symbols is the
one-element sequence $`(f)`. No other core op refers to a symbol.

$$`\mathrm{refs}(\mathsf{call}~f : t^* \to r^*) = (f)`

$$`\mathrm{refs}(\mathit{op}) = \epsilon \ \text{ for every other op}`

The general rules check that $`f` names a function of the module.
:::

:::readable Fir.Core.Op.Valid (fingerprint := "11703554325319780839")
*Definition: the core rules of an op.* Beyond its signature, which the
{ref "The-fir-specification--Validation--The-general-rules"}[general rules]
check, a core op obeys these rules in its op context $`C`:

$$`\frac{t^* = \mathrm{results}_C}{C \vdash \mathsf{ret}~t^*~\text{valid}}`

$$`\frac{\mathrm{symtab}_C(f) = (t^* \to r^*)}{C \vdash \mathsf{call}~f : t^* \to r^*~\text{valid}}`

$$`\frac{M < N}{C \vdash \mathsf{zext}_{M \to N}~\text{valid}}`

$$`\frac{M < N}{C \vdash \mathsf{sext}_{M \to N}~\text{valid}}`

$$`\frac{N < M}{C \vdash \mathsf{trunc}_{M \to N}~\text{valid}}`

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

Every other op has no rule beyond its signature. These three definitions
are what the core dialect
{ref "The-fir-specification--Validation--Scope-and-symbols"}[adds to validation].
:::
