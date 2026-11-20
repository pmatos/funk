import VersoManual
import Fir.Core.MemCopyPoison
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the copy and move poison
obligations, which renders `Fir.Core.MemCopyPoison`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "Copy and move poison obligations: readable blocks" =>

:::moduleDocs (fingerprint := "11372635642308506761")
:::

:::readable Fir.Core.fillPtr Fir.Core.copyUnits_ub_of_noProv Fir.Core.copyStep_ub_of_noProv Fir.Core.copyLenRule_ub_fill (pin := Fir.Core.copyLenRule) (pin := Fir.copyUnits) (fingerprint := "1285946363963922073")
*Theorems: a poison pointer is filled by one with no provenance.* Let
$`\mathrm{fill}(p)` be $`p` for a pointer and the pointer with no
provenance and offset 0 for poison. A copy of units through a pointer with
no provenance, the destination or the source, is UB from any memories.
So, for a length other than 0, the rule's step after the poison check is
UB through such a pointer, by the overlap check or by the copy of units.
Hence wherever the rule of a defined length is UB from the memories
$`S`, it is UB from $`S` on $`\mathrm{fill}(p)` and $`\mathrm{fill}(q)`.
:::

:::readable Fir.Core.memCopy_makesNoPoison Fir.Core.memCopy_memPropagates Fir.Core.memCopy_memReturnsOnDefined (pin := Fir.MakesNoPoison) (pin := Fir.MemPropagatesPoison) (pin := Fir.MemReturnsOnDefined) (fingerprint := "8643387725823249149")
*Theorems: a copy or a move propagates poison.* $`\mathsf{memCopy}_N~k~o~W`
gives no result, so it makes no poison, and a poison operand gives no
poison result. It meets the
{ref "The-fir-specification--Memory--Poison-obligations-with-memory"}[poison obligations with memory]:
where it is UB from $`S` on a poison operand, it is UB from $`S` on the
defined operands that put the chosen length in place of a poison length
and $`\mathrm{fill}` of each poison pointer. And on the defined operands
of two pointers with no provenance and a length of 0 it returns, from
memories inside a call.
:::
