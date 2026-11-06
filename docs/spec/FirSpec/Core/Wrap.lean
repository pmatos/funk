import VersoManual
import Fir.Core.Wrap
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on wrap flag rules, which renders
`Fir.Core.Wrap` (ADR-2026-11-05-2012). Each block explains declarations of
that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Wrap flag rules: readable blocks" =>

:::readable Fir.Core.subValues Fir.Core.mulValues (pin := BitVec.sub) (pin := BitVec.mul) (fingerprint := "186644350761562636")
*Definition: the rules of $`\mathsf{sub}` and $`\mathsf{mul}` without
flags.* For every width $`N`, $`\mathsf{sub}_N` of two vectors of bits is
their difference modulo $`2^N`, and $`\mathsf{mul}_N` their product modulo
$`2^N`. A poison operand, in either place, gives poison:

$$`\begin{aligned} \mathsf{sub}_N(a, b) &= (a - b) \bmod 2^N \\ \mathsf{mul}_N(a, b) &= (a \cdot b) \bmod 2^N \end{aligned}`

for $`a` and $`b` in $`\mathbb{B}^N`, the set of vectors of $`N` bits,
and both are poison when $`a` or $`b` is poison. A vector of bits stands for the number it writes in binary, and
$`k \bmod 2^N` for the vector that writes the remainder of $`k` divided by
$`2^N`, as in the
{ref "The-fir-specification--Execution--Arithmetic-rules"}[arithmetic rules].
Like $`\mathsf{add}`, both wrap as two's complement does, are never UB, and
{ref "The-fir-specification--Execution--Poison-classes"}[propagate poison]
(ADR-2026-10-30-0818).
:::

:::readable Fir.Core.wrapValues (pin := Fir.Core.WrapFlags) (fingerprint := "8525004174366977493")
*Definition: an op with wrap flags.* Take a set $`\phi` of
{ref "The-fir-specification--Abstract-syntax--Core-ops"}[wrap flags], two
overflow tests $`o_u` and $`o_s` on pairs of vectors of $`N` bits, and a rule $`g`
on two values of $`\mathsf{i}N`. On two vectors $`a` and $`b`, the op with
the flags $`\phi` gives poison when a flag is broken, and $`g(a, b)`
otherwise. On a poison operand it gives $`g(a, b)`. It is written
$`\mathrm{wrap}(\phi, o_u, o_s, g)`, and it is the rule $`h` with:

$$`h(a, b) = \begin{cases} \mathsf{poison} & \text{if a flag is broken} \\ g(a, b) & \text{otherwise} \end{cases}`

A flag is broken when $`a` and $`b` are vectors of bits and
$`\mathsf{nuw} \in \phi` and $`o_u(a, b)` holds, or $`\mathsf{nsw} \in \phi`
and $`o_s(a, b)` holds. Each flag is a promise
about the operands, and a broken promise gives poison, not UB
(ADR-2026-10-29-2006). One definition serves $`\mathsf{add}`,
$`\mathsf{sub}` and $`\mathsf{mul}` at every width.
:::

:::readable Fir.Core.addWith Fir.Core.subWith Fir.Core.mulWith (pin := Fir.Core.wrapValues) (pin := BitVec.uaddOverflow) (pin := BitVec.saddOverflow) (pin := BitVec.usubOverflow) (pin := BitVec.ssubOverflow) (pin := BitVec.umulOverflow) (pin := BitVec.smulOverflow) (fingerprint := "10585219860027332993")
*Definition: the rules of $`\mathsf{add}`, $`\mathsf{sub}` and
$`\mathsf{mul}` with flags.* For every width $`N` and set of flags
$`\phi`, each op is $`\mathrm{wrap}` of its rule without flags, with the
two tests that its exact result does not fit in $`N` bits:

$$`\begin{aligned} \mathsf{add}_N~\phi &= \mathrm{wrap}(\phi, o^{+}_u, o^{+}_s, \mathsf{add}_N) \\ \mathsf{sub}_N~\phi &= \mathrm{wrap}(\phi, o^{-}_u, o^{-}_s, \mathsf{sub}_N) \\ \mathsf{mul}_N~\phi &= \mathrm{wrap}(\phi, o^{\cdot}_u, o^{\cdot}_s, \mathsf{mul}_N) \end{aligned}`

On the right, $`\mathsf{add}_N` is the rule of the
{ref "The-fir-specification--Execution--Arithmetic-rules"}[arithmetic rules],
and $`\mathsf{sub}_N` and $`\mathsf{mul}_N` those above. For
$`\odot` one of $`+`, $`-` and $`\cdot`, computed exactly on integers:

$$`\begin{aligned} o^{\odot}_u(a, b) &\iff a \odot b \notin [0,\, 2^N - 1] \\ o^{\odot}_s(a, b) &\iff \mathrm{signed}_N(a) \odot \mathrm{signed}_N(b) \\ &\phantom{\iff} \notin [-2^{N-1},\, 2^{N-1} - 1] \end{aligned}`

Here $`\mathrm{signed}_N(a)` is the integer that $`a` writes in two's
complement: $`a` when its top bit is 0, and $`a - 2^N` when it is 1. So
$`\mathsf{nuw}` promises that the exact result, read as unsigned, fits, and
$`\mathsf{nsw}` that it fits read as signed. With both, either broken
promise gives poison. At $`\mathsf{i1}` the signed values are 0 and
$`-1`, so $`\mathsf{add}_1~\{\mathsf{nsw}\}(1, 1)` is poison: its exact
signed result, $`-2`, does not fit.
:::

:::readable Fir.Core.addWith_none (fingerprint := "12337429332899228685")
*Theorem: with no flags, $`\mathsf{add}` is the rule of the arithmetic
rules section.* For every width $`N` and all values $`a` and $`b` of
$`\mathsf{i}N`, poison included:

$$`\mathsf{add}_N~\emptyset\,(a, b) = \mathsf{add}_N(a, b)`

On the left is the rule above with the empty set of flags, and on the right
the rule of the
{ref "The-fir-specification--Execution--Arithmetic-rules"}[arithmetic rules].
The core dialect runs every $`\mathsf{add}` by the rule with flags; this
theorem says that an $`\mathsf{add}` without flags still means what the
earlier rule says.
:::

:::readable Fir.Core.WrapFlags.all (pin := Fir.Core.WrapFlags) (fingerprint := "5422977218104886877")
*Definition: every set of flags, for the tests.* The list of the four sets
of flags: $`\emptyset`, $`\{\mathsf{nuw}\}`, $`\{\mathsf{nsw}\}` and
$`\{\mathsf{nuw}, \mathsf{nsw}\}`. The tests of this section run the ops
with each of them.
:::
