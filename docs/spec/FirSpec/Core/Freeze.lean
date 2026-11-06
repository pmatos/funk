import VersoManual
import Fir.Core.Freeze
import Fir.Execution.ChoiceTree
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the freeze rule, which renders
`Fir.Core.Freeze` (ADR-2026-11-05-2012). Each block explains declarations of
that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "The freeze rule: readable blocks" =>

:::readable Fir.Core.freezeValue (pin := Fir.MonadChoice) (pin := Fir.SetM.instMonadChoice) (pin := Fir.ChoiceTree.instMonadChoice) (fingerprint := "1188688411120997030")
*Definition: the rule of $`\mathsf{freeze}`.* For every width $`N`, for
every way of computing with the
{ref "The-fir-specification--Execution--Effects-and-op-semantics"}[choice effect],
$`\mathsf{freeze}_N` of a vector of bits gives that vector, and
$`\mathsf{freeze}_N` of poison chooses $`N` arbitrary bits, once, and gives
them:

$$`\mathsf{freeze}_N(a) = \begin{cases} a & \text{if } a \in \mathbb{B}^N \\ \mathrm{choose}(N) & \text{if } a \text{ is poison} \end{cases}`

Here $`\mathbb{B}^N` is the set of vectors of $`N` bits, and
$`\mathrm{choose}(N)` gives $`N` arbitrary bits: in the
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[set of the ways a run may end]
it may end with any of them, so a run goes on in $`2^N` ways, one for
each, and in the tree of choices that `fir-ref` walks it is one choice of
$`N` bits. The result is never poison, and the
rule is never UB.

$`\mathsf{freeze}` is how a program stops poison (ADR-2026-10-29-2006). The
choice is made once per run of the op: the interpreter binds the op's
result to the bits chosen, so every use of the result sees the same bits,
and $`\mathsf{sub}` of a frozen poison from itself is 0. Another
$`\mathsf{freeze}` of the same poison chooses again, and may choose other
bits (ADR-2026-10-29-2017).
:::
