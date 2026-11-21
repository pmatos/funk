import VersoManual
import Fir.Core.PtrIntLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the obligations of pointers as integers, which
renders `Fir.Core.PtrIntLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Pointers as integers: obligations: readable blocks" =>

:::moduleDocs (fingerprint := "6581734986452472472")
:::

:::readable Fir.Core.finitelyMany_map Fir.Core.exposeAt Fir.Core.fromAddrAt (fingerprint := "25967292377303784")
*Definitions and lemma.* Mapping the results of a computation keeps
finitely many outcomes. $`\mathrm{exposeAt}(q)` is the exposure that the
rule of $`\mathsf{ptr\_expose}` runs on the pointer $`q`, and
$`\mathrm{fromAddrAt}(a)` the turning back of the address $`a` that the
rule of $`\mathsf{ptr\_from\_int}` runs, each in the memory $`\rho(N)` under
the run's policy or resolver.
:::

:::readable Fir.Core.ptrExposeRule_cases Fir.Core.ptrFromIntRule_cases Fir.Core.ptrExpose_ownRuleHas Fir.Core.ptrFromInt_ownRuleHas Fir.Core.ne_of_not_has (pin := Fir.OwnRuleHas) (fingerprint := "6610438743820800795")
*Lemmas: the shape of the rules.* A property holds of the rule of
$`\mathsf{ptr\_expose}` when it holds of UB and of each exposure with its
result mapped, and of the rule of $`\mathsf{ptr\_from\_int}` when it holds
of each turning back of an integer with its result mapped. What each op
runs by its own rule then has the property. A memory that an op of the
memory $`N` does not declare is not $`\rho(N)`.
:::

:::readable Fir.Core.ptrExpose_writesNot Fir.Core.ptrExpose_readsNot Fir.Core.ptrExpose_allocatesNot Fir.Core.ptrExpose_exposesNot Fir.Core.ptrExpose_rebuildsNot (pin := Fir.WritesNot) (pin := Fir.ReadsNot) (pin := Fir.AllocatesNot) (pin := Fir.ExposesNot) (pin := Fir.RebuildsNot) (fingerprint := "2693061827339649108")
*Theorems: what $`\mathsf{ptr\_expose}` touches.* Wherever a run names the
core's memories, $`\mathsf{ptr\_expose}` writes no unit of any memory and
neither allocates nor frees in any; it reads no memory but $`\rho(N)`, the
memory it declares; it gives an address in no memory but $`\rho(N)`, where
it declares an allocation; and it counts no integer turned back into a
pointer in any memory.
:::

:::readable Fir.Core.ptrFromInt_writesNot Fir.Core.ptrFromInt_readsNot Fir.Core.ptrFromInt_allocatesNot Fir.Core.ptrFromInt_exposesNot Fir.Core.ptrFromInt_rebuildsNot (pin := Fir.WritesNot) (pin := Fir.ReadsNot) (pin := Fir.AllocatesNot) (pin := Fir.ExposesNot) (pin := Fir.RebuildsNot) (fingerprint := "8515576620775580698")
*Theorems: what $`\mathsf{ptr\_from\_int}` touches.* Wherever a run names
the core's memories, $`\mathsf{ptr\_from\_int}` writes no unit of any
memory, neither allocates nor frees in any, and gives no address in any; it
reads no memory but $`\rho(N)`, and counts a call in no memory but
$`\rho(N)`, where it declares an allocation.
:::

:::readable Fir.Core.ptrExpose_finitelyMany Fir.Core.ptrFromInt_finitelyMany Fir.Core.ptrExpose_memTotal Fir.Core.ptrFromInt_memTotal (pin := Fir.FinitelyMany) (pin := Fir.MemTotal) (fingerprint := "1579953152469654805")
*Theorems: totality and finitely many outcomes.* From any memories, each op
has an outcome, and at most one that ends.
:::

:::readable Fir.Core.ptrFromInt_neverUB Fir.Core.ptrExpose_makesNoPoison Fir.Core.ptrFromInt_makesNoPoison (pin := Fir.NeverUB) (pin := Fir.MakesNoPoison) (fingerprint := "8183493211294246671")
*Theorems: no UB and no poison where none is declared.*
$`\mathsf{ptr\_from\_int}` never ends in UB. On a defined operand,
$`\mathsf{ptr\_expose}` gives a defined integer and
$`\mathsf{ptr\_from\_int}` a defined pointer.
:::

:::readable Fir.Core.fromAddrAt_refines Fir.Core.ptrExpose_memMonotone Fir.Core.ptrFromInt_memMonotone (pin := Fir.StateRefinedBy) (pin := Fir.MemMonotone) (fingerprint := "14766950545343260945")
*Theorems: monotonicity.* Two turnings back of integers, each with its
result mapped, refine each other whenever every result of the one is
related to every result of the other: each counts the call in the same
memory, so from memories that refine each other the memories after do too.
So $`\mathsf{ptr\_from\_int}` is monotone with memory: on the same integer
it gives the same pointer, and on a poison integer poison, which every
pointer refines. $`\mathsf{ptr\_expose}` is monotone too: a poison pointer
is UB, which every outcome refines, and on the same pointer, exposures in
memories that refine each other give the same integer, or UB in both.
:::

:::readable Fir.Core.ptrFromInt_memPropagates Fir.Core.ptrFromInt_memReturnsOnDefined (pin := Fir.MemPropagatesPoison) (pin := Fir.MemReturnsOnDefined) (fingerprint := "15921963675677798649")
*Theorems: $`\mathsf{ptr\_from\_int}` propagates poison.* A poison integer
gives a poison pointer, and the op is never UB, so it is UB by its own rules
alone; and it gives a result on a defined integer, from memories inside a
call. $`\mathsf{ptr\_expose}` is an exception, with no poison obligation.
:::
