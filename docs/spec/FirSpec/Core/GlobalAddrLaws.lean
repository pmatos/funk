import VersoManual
import Fir.Core.GlobalAddrLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on global address obligations, which
renders `Fir.Core.GlobalAddrLaws` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Global address obligations: readable blocks" =>

:::moduleDocs (fingerprint := "18201747163340802579")
:::

:::readable Fir.Core.globalAddr_denote Fir.Core.globalAddr_ownRuleHas (pin := Fir.Core.memDenoteAt) (pin := Fir.Core.globalAddrResult) (fingerprint := "17284928555500596725")
*Theorems: $`\mathsf{globaladdr}` with memory.* In the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] over
the set monad, at every layout, naming and record $`L` of the items a run
gives, the meaning of $`\mathsf{globaladdr}~s~N` is its result where $`L`
places $`s`, a computation of the set monad run in the layer: it keeps the
memories. So what it runs has every property that each such computation
has.
:::

:::readable Fir.Core.globalAddr_writesNot Fir.Core.globalAddr_readsNot Fir.Core.globalAddr_allocatesNot Fir.Core.globalAddr_ignoresMemory Fir.Core.globalAddr_finitelyMany (pin := Fir.WritesNot) (pin := Fir.ReadsNot) (pin := Fir.AllocatesNot) (pin := Fir.IgnoresMemory) (pin := Fir.FinitelyMany) (fingerprint := "4396779072566097235")
*Theorems: $`\mathsf{globaladdr}` touches no memory.* By its own rule,
$`\mathsf{globaladdr}` writes no unit of any memory, reads none, allocates
in none, ends with the memories it started with and the same result from
any others, and has one outcome from any memories.
:::

:::readable Fir.Core.globalAddrResult_defined Fir.Core.globalAddr_neverUB Fir.Core.globalAddr_makesNoPoison Fir.Core.globalAddr_memTotal Fir.Core.globalAddr_memMonotone (pin := Fir.Core.globalAddrValue) (pin := Fir.NeverUB) (pin := Fir.MakesNoPoison) (pin := Fir.MemTotal) (pin := Fir.MemMonotone) (fingerprint := "15556265228726386682")
*Theorems: $`\mathsf{globaladdr}` is pure, total and monotone with
memory.* For every symbol and memory, and every record of items, the
result of $`\mathsf{globaladdr}` is a pointer, never poison; it never ends
in UB, has an outcome from any memories, and is
{ref "The-fir-specification--Memory--Monotonicity-with-memory"}[monotone with memory]:
it takes no operands, so it gives the same pointer from memories that
refine others. None of these asks anything of the record: a global it
does not place gives the pointer with no provenance.
:::

:::readable Fir.Core.globalAddr_memPropagates Fir.Core.globalAddrNoArgs Fir.Core.globalAddr_memReturnsOnDefined (pin := Fir.MemPropagatesPoison) (pin := Fir.MemReturnsOnDefined) (fingerprint := "6270317597999269340")
*Theorems: $`\mathsf{globaladdr}` propagates poison with memory.* It has no
operand that could be poison, and it is never UB, so it meets both poison
clauses with memory. On its empty operand vector it returns a result from
memories inside a call.
:::
