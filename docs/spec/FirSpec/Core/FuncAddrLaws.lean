import VersoManual
import Fir.Core.FuncAddrLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on function address obligations, which
renders `Fir.Core.FuncAddrLaws` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Function address obligations: readable blocks" =>

:::moduleDocs (fingerprint := "10663078352554116809")
:::

:::readable Fir.Core.funcAddr_denote Fir.Core.funcAddr_ownRuleHas (pin := Fir.Core.memDenoteAt) (pin := Fir.Core.funcAddrResult) (fingerprint := "9103799788234015501")
*Theorems: $`\mathsf{funcaddr}` with memory.* In the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] over
the set monad, at every layout, naming and record $`L` of the items a run
gives, the meaning of $`\mathsf{funcaddr}~f~N` is its result where $`L`
places $`f`, a computation of the set monad run in the layer: it keeps the
memories. So what it runs has every property that each such computation
has.
:::

:::readable Fir.Core.funcAddr_writesNot Fir.Core.funcAddr_readsNot Fir.Core.funcAddr_allocatesNot Fir.Core.funcAddr_ignoresMemory Fir.Core.funcAddr_finitelyMany (pin := Fir.WritesNot) (pin := Fir.ReadsNot) (pin := Fir.AllocatesNot) (pin := Fir.IgnoresMemory) (pin := Fir.FinitelyMany) (fingerprint := "11445042753917978692")
*Theorems: $`\mathsf{funcaddr}` touches no memory.* By its own rule,
$`\mathsf{funcaddr}` writes no unit of any memory, reads none, allocates
in none, ends with the memories it started with and the same result from
any others, and has one outcome from any memories.
:::

:::readable Fir.Core.funcAddrResult_defined Fir.Core.funcAddr_neverUB Fir.Core.funcAddr_makesNoPoison Fir.Core.funcAddr_memTotal Fir.Core.funcAddr_memMonotone (pin := Fir.Core.funcAddrValue) (pin := Fir.NeverUB) (pin := Fir.MakesNoPoison) (pin := Fir.MemTotal) (pin := Fir.MemMonotone) (fingerprint := "7364512228540180018")
*Theorems: $`\mathsf{funcaddr}` is pure, total and monotone with
memory.* For every symbol and memory, and every record of items, the
result of $`\mathsf{funcaddr}` is a pointer, never poison; it never ends
in UB, has an outcome from any memories, and is
{ref "The-fir-specification--Memory--Monotonicity-with-memory"}[monotone with memory]:
it takes no operands, so it gives the same pointer from memories that
refine others. None of these asks anything of the record: a function it
does not place, or a result of a memory other than 0, gives the pointer
with no provenance.
:::

:::readable Fir.Core.funcAddr_memPropagates Fir.Core.funcAddrNoArgs Fir.Core.funcAddr_memReturnsOnDefined (pin := Fir.MemPropagatesPoison) (pin := Fir.MemReturnsOnDefined) (fingerprint := "17332816646015961181")
*Theorems: $`\mathsf{funcaddr}` propagates poison with memory.* It has no
operand that could be poison, and it is never UB, so it meets both poison
clauses with memory. On its empty operand vector it returns a result from
memories inside a call.
:::
