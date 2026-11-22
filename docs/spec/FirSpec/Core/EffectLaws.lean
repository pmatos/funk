import VersoManual
import Fir.Core.EffectLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the core dialect's effect
obligations, which renders `Fir.Core.EffectLaws` (ADR-2026-11-05-2012).
Each block explains declarations of that module and pins their
fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "The core dialect's effect obligations: readable blocks" =>

:::moduleDocs (fingerprint := "15187118450536989398")
:::

:::readable Fir.Core.Op.neverUB_all (pin := Fir.Core.Op.effects) (pin := Fir.NeverUBSetM) (fingerprint := "18098656012515844890")
*Theorem: each core op that does not declare may-UB never ends in UB in
the set monad.*
Every core op but $`\mathsf{sdiv}`, $`\mathsf{udiv}`, $`\mathsf{srem}`,
$`\mathsf{urem}`, $`\mathsf{cond\_br}`, $`\mathsf{unreachable}`, and
the loads and stores of an integer, a pointer or a float, and
$`\mathsf{memcpy}`, $`\mathsf{memmove}`, $`\mathsf{memset}` and
$`\mathsf{ptr\_expose}`, which declare may-UB,
never ends
in UB, at every width. Each rule gives its result at once,
$`\mathsf{freeze}`, the float arithmetic and the conversions from
integers and between formats after choosing bits, and $`\mathsf{br}` and
$`\mathsf{ret}` go to their successor or return. $`\mathsf{call}` has no
rule of its own, and
$`\mathsf{alloca}`, $`\mathsf{fieldaddr}` and
$`\mathsf{ptr\_from\_int}` none in the set monad, so none of them has an
outcome by one.
:::

:::readable Fir.Core.defined₁ Fir.Core.defined₂ Fir.Core.not_any_of_ne (pin := Fir.HVector.Any) (pin := Fir.Core.Ty.IsPoison) (fingerprint := "17464123918340822883")
*Theorems: defined operands hold values.* An operand vector of one or two
integers with no poison element holds values: $`(v)` is
$`(\mathsf{value}~x)` for some $`x`, and $`(v_1, v_2)` is
$`(\mathsf{value}~x, \mathsf{value}~y)`. A vector of one integer that is
not poison has no poison element.
:::

:::readable Fir.Core.defined₂Float Fir.Core.not_any_of_ne_float (pin := Fir.HVector.Any) (pin := Fir.Core.Ty.IsPoison) (fingerprint := "9456831933011364645")
*Theorems: defined float operands hold values.* An operand vector of two
floats of one format with no poison element holds values,
$`(\mathsf{value}~x, \mathsf{value}~y)`; and a vector of one float that
is not poison has no poison element. The proofs for $`\mathsf{fcmp}` and
the float $`\mathsf{const}` use them, as those for $`\mathsf{icmp}` and
the integer $`\mathsf{const}` use the theorems above.
:::

:::readable Fir.Core.ruleOfEv_divEv_defined (pin := Fir.Core.divEv) (pin := Fir.Core.ruleOfEv) (fingerprint := "657474154116654491")
*Theorem: a division whose quotient is defined makes no poison.* If the
quotient $`q(x, y)` is a value for all $`x` and $`y`, then on two values
$`\mathsf{value}~x` and $`\mathsf{value}~y` the division with that
quotient, when it gives a result, gives a value.
:::

:::readable Fir.Core.flags_none (fingerprint := "9505051277240368478")
*Theorem: an instance of $`\mathsf{add}`, $`\mathsf{sub}` or
$`\mathsf{mul}` that does not declare $`\mathsf{mayPoison}` has no flags.*
Its flags $`f` are neither $`\mathsf{nuw}` nor $`\mathsf{nsw}`.
:::

:::readable Fir.Core.Op.makesNoPoison_all (pin := Fir.Core.Op.effects) (pin := Fir.MakesNoPoisonSetM) (fingerprint := "15943501881943734980")
*Theorem: each core op that does not declare $`\mathsf{mayPoison}` makes no
poison in the set monad.* On operands with no poison, $`\mathsf{const}`, $`\mathsf{add}`,
$`\mathsf{sub}` and $`\mathsf{mul}` without flags, $`\mathsf{sdiv}` and
$`\mathsf{udiv}` without $`\mathsf{exact}`, $`\mathsf{srem}`,
$`\mathsf{urem}`, the bitwise ops, $`\mathsf{icmp}`,
$`\mathsf{select}`, the width changes, $`\mathsf{freeze}`, the float
$`\mathsf{const}`, $`\mathsf{fcmp}` and the float arithmetic without
$`\mathsf{nnan}` and $`\mathsf{ninf}`, the bit casts, the conversions from integers, the conversions between formats and $`\mathsf{ptradd}` give defined results, at every width and format. $`\mathsf{select}` chooses one of its defined operands,
$`\mathsf{freeze}` gives bits, and a float op's NaN, and a zero of either
sign under $`\mathsf{nsz}`, are defined bits too: without those two
flags no operand breaks a flag. $`\mathsf{call}` gives no result by a rule
of its own, $`\mathsf{alloca}`, the stores of an integer, a pointer or
a float, $`\mathsf{fieldaddr}`, the copies and moves, the fills,
$`\mathsf{ptr\_expose}` and $`\mathsf{ptr\_from\_int}` none in the set
monad, and the terminators give none. The loads of
an integer, a pointer or a float declare $`\mathsf{mayPoison}`, so the
obligation asks nothing of them.
:::

:::readable Fir.Core.Op.notControl_all (pin := Fir.Core.Op.effects) (fingerprint := "1921785165412561646")
*Theorem: each core op that does not declare $`\mathsf{control}` is not a
terminator.* The core terminators are $`\mathsf{br}`,
$`\mathsf{cond\_br}`, $`\mathsf{ret}` and $`\mathsf{unreachable}`, and each
declares
$`\mathsf{control}`.
:::

:::readable Fir.Core.lawfulDialectEffects (pin := Fir.LawfulDialectEffects) (fingerprint := "172079627767923088")
*Theorem: the core dialect is lawful in its effects.* Every effect that a
core op leaves out, it does not have. Every core op but
$`\mathsf{alloca}`, the loads and stores, $`\mathsf{fieldaddr}`, the
copies and moves, the fills, $`\mathsf{ptr\_expose}` and
$`\mathsf{ptr\_from\_int}` touches no memory and reads no item: each is
{ref "The-fir-specification--Memory--The-core___s-rules-with-memory"}[tied],
running with memory by its rule in the set monad and keeping the memories.
So for each such op, the three theorems above carry from the set monad to
the semantics with memory by that op's own tie, and so do the memory
obligations, which every computation with no memory meets.
$`\mathsf{alloca}` meets each obligation by
{ref "The-fir-specification--Memory--Stack-allocation-obligations"}[its own rule with memory]:
it is never UB, its result is never poison, it writes and reads no memory,
and it allocates only in the memory of its result. $`\mathsf{load}` meets
each by
{ref "The-fir-specification--Memory--Load-obligations"}[its own rule with memory]:
it writes no memory, allocates in none and reads only the memory of its
pointer, and it declares may-UB and may produce poison. $`\mathsf{store}`
meets each by
{ref "The-fir-specification--Memory--Store-obligations"}[its own rule with memory]:
it writes only the memory of its pointer, reads none, its own included,
allocates in none, makes no poison, since it gives no result, and declares
may-UB. The loads and stores of a pointer and of a float meet each as
$`\mathsf{load}` and $`\mathsf{store}` do. $`\mathsf{fieldaddr}` meets each by
{ref "The-fir-specification--Memory--Field-address-obligations"}[its own rule with memory]:
it is never UB, its result is poison only on a poison operand, and it
writes, reads and allocates in no memory, as its empty effect set
declares. $`\mathsf{memcpy}` and $`\mathsf{memmove}` meet each by
{ref "The-fir-specification--Memory--Copy-and-move-obligations"}[their own rule with memory]:
they write and read only the memory of their pointers, allocate in none,
make no poison, since they give no result, and declare may-UB.
$`\mathsf{memset}` meets each by
{ref "The-fir-specification--Memory--Fill-obligations"}[its own rule with memory],
as $`\mathsf{store}` does. $`\mathsf{ptr\_expose}` and
$`\mathsf{ptr\_from\_int}` meet each by
{ref "The-fir-specification--Memory--Pointers-as-integers-obligations"}[their own rules with memory]:
they write no memory, allocate or free nothing, read only the memory of
their pointer, and give defined results on defined operands;
$`\mathsf{ptr\_expose}` declares may-UB, and $`\mathsf{ptr\_from\_int}`
is never UB. So a pass
may rely on the core ops' effect sets (ADR-2026-11-09-1541).
:::
