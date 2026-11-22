import VersoManual
import Fir.Core.FieldAddrLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on field address obligations, which
renders `Fir.Core.FieldAddrLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Field address obligations: readable blocks" =>

:::moduleDocs (fingerprint := "3837551866316034595")
:::

:::readable Fir.Core.fieldAddr_denote Fir.Core.fieldAddr_ownRuleHas (pin := Fir.Core.memDenoteAt) (pin := Fir.Core.fieldAddrResult) (fingerprint := "16347293802887180548")
*Theorems: $`\mathsf{fieldaddr}` with memory.* In the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] over
the set monad, at every layout, naming and record $`L` of the items a run
gives, the meaning of $`\mathsf{fieldaddr}~s~j~N~w` is its result in the
layout $`L(s)`, a computation of the set monad run in the layer: it keeps
the memories. So what it runs has every property that each such
computation has.
:::

:::readable Fir.Core.fieldAddr_writesNot Fir.Core.fieldAddr_readsNot Fir.Core.fieldAddr_allocatesNot Fir.Core.fieldAddr_ignoresMemory Fir.Core.fieldAddr_finitelyMany (pin := Fir.WritesNot) (pin := Fir.ReadsNot) (pin := Fir.AllocatesNot) (pin := Fir.IgnoresMemory) (pin := Fir.FinitelyMany) (fingerprint := "1751219421586350006")
*Theorems: $`\mathsf{fieldaddr}` touches no memory.* By its own rule,
$`\mathsf{fieldaddr}` writes no unit of any memory, reads none, allocates
in none, ends with the memories it started with and the same result from
any others, and has one outcome from any memories.
:::

:::readable Fir.Core.fieldAddrResult_poison Fir.Core.fieldAddrResult_defined Fir.Core.fieldAddrResult_isRefinedBy (pin := Fir.Core.fieldAddrValue) (pin := Fir.Core.elemAddrValue) (fingerprint := "15429627891656503254")
*Theorems: the result of $`\mathsf{fieldaddr}` is strict and keeps
refinement.* A poison operand gives a poison pointer, a pointer and an
index that are not poison give a pointer, and on operands that refine
others the result refines the other's: poison is refined by every pointer,
and a pointer or an integer only by itself.
:::

:::readable Fir.Core.fieldAddr_neverUB Fir.Core.fieldAddr_makesNoPoison Fir.Core.fieldAddr_memTotal Fir.Core.fieldAddr_memMonotone (pin := Fir.NeverUB) (pin := Fir.MakesNoPoison) (pin := Fir.MemTotal) (pin := Fir.MemMonotone) (fingerprint := "17119794483195446014")
*Theorems: $`\mathsf{fieldaddr}` is pure, total and monotone with memory.*
For every symbol, field, memory and index width, and every record of
items, $`\mathsf{fieldaddr}` never ends in UB, gives a pointer on operands
that are not poison, has an outcome from any memories, and is
{ref "The-fir-specification--Memory--Monotonicity-with-memory"}[monotone with memory].
None of these asks anything of the record: a layout or field it does not
give moves the pointer by 0.
:::

:::readable Fir.Core.fieldAddr_memPropagates Fir.Core.fieldAddrZero Fir.Core.fieldAddr_memReturnsOnDefined (pin := Fir.MemPropagatesPoison) (pin := Fir.MemReturnsOnDefined) (fingerprint := "9447603566033993853")
*Theorems: $`\mathsf{fieldaddr}` propagates poison with memory.* A poison
operand gives a poison pointer, and it is never UB, so it meets both
poison clauses with memory. On the pointer with no provenance at offset 0,
and the index 0 when it takes one, it returns a result from memories
inside a call.
:::
