import VersoManual
import Fir.Core.Branch
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on branch rules, which renders
`Fir.Core.Branch` (ADR-2026-11-05-2012). Each block explains declarations of
that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Branch rules: readable blocks" =>

:::readable Fir.Core.brExit (pin := Fir.Exit) (fingerprint := "1268996599905063284")
*Definition: the rule of $`\mathsf{br}`.* $`\mathsf{br}` goes to its
successor with index 0, its only one, on every run:

$$`\mathrm{exit}_{\mathsf{br}}() = \mathsf{goto}~0`

Here $`\mathrm{exit}_o` is
{ref "The-fir-specification--Execution--Effects-and-op-semantics"}[where control goes]
when the terminator $`o` ends its block, and $`\mathsf{goto}~i` says: go to
the successor with index $`i`, counting from 0. $`\mathsf{br}` has no
operands: the values that it passes are its successor's, and the
{ref "The-fir-specification--Execution--The-interpreter"}[interpreter]
binds them to the arguments of the block that the successor names, poison
included.
:::

:::readable Fir.Core.condBrExit (pin := Fir.Exit) (pin := Fir.Ev) (fingerprint := "8548291126789120834")
*Definition: the rule of $`\mathsf{cond\_br}`.* $`\mathsf{cond\_br}`
(`condBr` in the Lean) takes an $`\mathsf{i1}` condition $`c`. It goes to
its first successor when $`c` is 1 and to its second when $`c` is 0, and a
poison condition is immediate UB, with the reason `cond_br on poison`:

$$`\mathrm{exit}_{\mathsf{cond\_br}}(c) = \begin{cases} \mathsf{goto}~0 & \text{if } c = 1 \\ \mathsf{goto}~1 & \text{if } c = 0 \\ \text{UB} & \text{if } c \text{ is poison} \end{cases}`

A branch on poison is never a free choice between the successors: a
compiler learns facts from a branch, such as the condition being 1 in the
first successor, and those facts would be wrong if a branch on poison
could go either way, as the section on
{ref "The-fir-specification--Execution--Poison-and-immediate-UB"}[poison and immediate UB]
explains (ADR-2026-10-29-2006, ADR-2026-10-30-0818). The values that the
successors pass reach the block's arguments unchanged. $`\mathsf{cond\_br}`
ends in one of these ways and never chooses, so this definition is a
function to its ending.
:::

:::readable Fir.Core.exitOfEv (pin := Fir.Ev) (pin := Fir.MonadUB) (pin := Fir.Exit) (fingerprint := "15251266884827550953")
*Definition: a terminator's rule that may end with UB, for every way of
computing.* Let $`e` be a way a terminator ends: going to an exit $`x`, or
immediate UB with a reason $`r`. For every way of computing with the
{ref "The-fir-specification--Execution--Effects-and-op-semantics"}[UB effect],
the rule of $`e` is the computation that gives $`x` in the first case, and
$`\mathrm{ub}(r)` in the second. It turns the rule of
$`\mathsf{cond\_br}` above into the rule that the
{ref "The-fir-specification--Execution--Core-op-semantics"}[core op semantics]
gives the op.
:::
