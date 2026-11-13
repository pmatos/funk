import VersoManual
import Fir.Core.BranchLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on branch obligations, which renders
`Fir.Core.BranchLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Branch obligations: readable blocks" =>

:::moduleDocs (fingerprint := "9509901482889504764")
:::

:::readable Fir.Core.exitOfEv_iff (pin := Fir.Core.exitOfEv) (fingerprint := "2335364038614251743")
*Theorem: a terminator rule made from a way to end ends that way.* A step
in the proofs below. The
{ref "The-fir-specification--Execution--Branch-rules"}[branch rules] make
each way $`e` to end, a place to go or UB, into a terminator's rule. In
the set monad, that rule ends with $`e'` exactly when $`e' = e`.
:::

:::readable Fir.Core.br_exit Fir.Core.condBr_exit (pin := Fir.Core.brExit) (pin := Fir.Core.condBrExit) (pin := Fir.Core.Op.exit?) (pin := Fir.instDialectDenoteCoreDialectSetM) (fingerprint := "12193982817263337387")
*Theorem: where $`\mathsf{br}` and $`\mathsf{cond\_br}` go.* In the set
monad, $`\mathsf{br}` goes to its one successor and nowhere else, on every
operand vector $`\vec{v}`; $`\mathsf{cond\_br}` (`condBr` in the Lean) on a
condition $`c` goes to its first successor when $`c` is $`1`, to its
second when $`c` is $`0`, and is UB when $`c` is poison, and ends in no
other way:

$$`e \in \mathrm{exit}_{\mathsf{br}}(\vec{v}) \iff e = \mathsf{ok}~(\mathsf{goto}~0)`

$$`\begin{aligned} & e \in \mathrm{exit}_{\mathsf{cond\_br}}(c) \iff e = \\ & \quad \begin{cases} \mathsf{ok}~(\mathsf{goto}~0) & \text{if } c = 1 \\ \mathsf{ok}~(\mathsf{goto}~1) & \text{if } c = 0 \\ \mathsf{ub}~r & \text{if } c = \mathsf{poison} \end{cases} \end{aligned}`

where $`r` is the reason `cond_br on poison`. The proofs below read the
{ref "The-fir-specification--Execution--Branch-rules"}[branch rules]
through these two theorems.
:::

:::readable Fir.Core.br_total Fir.Core.br_monotone (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (fingerprint := "14788450786270107642")
*Theorem: $`\mathsf{br}` is total and monotone.* Under fir's execution
rules, $`\mathsf{br}` is
{ref "The-fir-specification--Execution--Poison-classes"}[total] and
{ref "The-fir-specification--Execution--Poison-classes"}[monotone]: on any
operands it goes to its one successor, so it has an exit everywhere, and
the same exit on operands that refine others. The values it passes to
the successor's block arguments are not its operands: the interpreter
passes them on as they are, poison included.
:::

:::readable Fir.Core.br_goto_lt (pin := Fir.Core.Op.succCount) (fingerprint := "3075993009042733143")
*Theorem: $`\mathsf{br}` goes only to a successor it has.* For every
operand vector, if the exit of $`\mathsf{br}` may be
$`\mathsf{ok}~(\mathsf{goto}~i)`, then $`i` is less than the number of
successors that validation gives $`\mathsf{br}`, which is one.
:::

:::readable Fir.Core.condBr_total Fir.Core.condBr_monotone (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (pin := Fir.Ev.IsRefinedBy) (fingerprint := "15160494712549368114")
*Theorem: $`\mathsf{cond\_br}` is total and monotone.* Under fir's
execution rules, $`\mathsf{cond\_br}` is
{ref "The-fir-specification--Execution--Poison-classes"}[total] and
{ref "The-fir-specification--Execution--Poison-classes"}[monotone].

It has an exit on every condition: a successor, or UB on poison. Where a
terminator goes is refined only by the same place, and UB allows
anything. So let $`c'` refine $`c`. If $`c` is poison,
$`\mathsf{cond\_br}` on $`c` is UB, which allows whatever it does on
$`c'`. Otherwise $`c'` is $`c`, and it goes to the same place.
:::

:::readable Fir.Core.condBr_goto_lt (pin := Fir.Core.Op.succCount) (fingerprint := "13851265096645987601")
*Theorem: $`\mathsf{cond\_br}` goes only to a successor it has.* For every
operand vector, if the exit of $`\mathsf{cond\_br}` may be
$`\mathsf{ok}~(\mathsf{goto}~i)`, then $`i` is less than the number of
successors that validation gives $`\mathsf{cond\_br}`, which is two.

No poison obligation says which successors an exit may name, and an exit
that names a successor the terminator lacks gets the run
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[stuck].
This theorem and the one for $`\mathsf{br}` are what the proofs that
{ref "The-fir-specification--Execution--Core-functions-without-calls"}[valid core functions]
never get stuck need of the branches.
:::
