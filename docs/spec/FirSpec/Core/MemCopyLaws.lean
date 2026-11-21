import VersoManual
import Fir.Core.MemCopyLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the copy and move obligations, which
renders `Fir.Core.MemCopyLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Copy and move obligations: readable blocks" =>

:::moduleDocs (fingerprint := "552254409804306718")
:::

:::readable Fir.Core.memCopy_denote (pin := Fir.Core.memCopyRule) (fingerprint := "14870968699586774585")
*Theorems: $`\mathsf{memcpy}` and $`\mathsf{memmove}` run by their rule.*
With memory, $`\mathsf{memCopy}_N~k~o~W` on the destination $`p`, the
source $`q` and the length $`l` runs the
{ref "The-fir-specification--Memory--Copy-and-move-rules"}[rule]
$`\mathrm{memcopy}_{k,W,N}(p, q, l)`.
:::

:::readable Fir.Core.copyLenRule_cases Fir.Core.memCopyRule_cases Fir.Core.memCopy_ownRuleHas (pin := Fir.Core.copyLenRule) (pin := Fir.OwnRuleHas) (fingerprint := "17411526622186744591")
*Theorems: the cases of the rule.* The rule of a defined length ends in
one of three ways: it returns no result at once, it is UB, or it is the
copy of units with no result. So a property holds of it when it holds of
those three. A property holds of the whole rule when it holds of the rule
of every defined length and a choice of bits keeps it; and it holds of
what the op runs by its own rule when it holds of the rule on every
operand vector.
:::

:::readable Fir.Core.memCopy_writesNot Fir.Core.memCopy_readsNot Fir.Core.memCopy_allocatesNot (pin := Fir.WritesNot) (pin := Fir.ReadsNot) (pin := Fir.AllocatesNot) (pin := Fir.Core.Op.effects) (fingerprint := "2982901870252984500")
*Theorems: a copy or a move touches only its own memory.* For every
memory $`x` other than $`\rho(N)`, the memory it declares that it reads
and writes, $`\mathsf{memCopy}_N~k~o~W` writes no unit of $`x` and does
not read $`x`; and for every memory $`x` it neither allocates nor frees
in $`x`. Each holds of the copy of units, of returning at once and of UB,
and a choice keeps it.
:::

:::readable Fir.Core.memCopy_memTotal Fir.Core.memCopy_finitelyMany (pin := Fir.MemTotal) (pin := Fir.FinitelyMany) (fingerprint := "16816578220659430383")
*Theorems: a copy or a move has an outcome, and finitely many.* From any
memories, $`\mathsf{memCopy}_N~k~o~W`
{ref "The-fir-specification--Memory--Totality-with-memory"}[has an outcome],
and it has
{ref "The-fir-specification--Memory--Ops-of-finitely-many-outcomes"}[finitely many]:
at most one that ends for each length, and a poison length chooses one of
$`2^W`.
:::

:::readable Fir.Core.copyLenRule_refines Fir.Core.memCopy_memMonotone (pin := Fir.StateRefinedBy) (pin := Fir.MemMonotone) (fingerprint := "16002821727998104183")
*Theorems: a copy or a move is monotone.* On the same length, pointers
that refine others give a rule that refines the others': a poison pointer
with a length other than 0 is UB, which every outcome refines, and equal
pointers make the same overlap check and a copy of units that refines from
refining memories. So $`\mathsf{memCopy}_N~k~o~W` is
{ref "The-fir-specification--Memory--Monotonicity-with-memory"}[monotone with memory]:
a defined length refines only itself, and a poison length may choose the
value that refines it.
:::
