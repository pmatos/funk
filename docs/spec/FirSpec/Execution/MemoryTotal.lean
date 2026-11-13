import VersoManual
import Fir.Execution.MemoryTotal
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on totality with memory, which renders
`Fir.Execution.MemoryTotal` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Totality with memory: readable blocks" =>

:::moduleDocs (fingerprint := "1072439918142219991")
:::

:::readable Fir.HasOutcome Fir.HasOutcome.map Fir.hasOutcome_lift Fir.HasOutcome.of_lift Fir.OpHasOutcome (fingerprint := "7856571833701684355")
*Definition and theorems: a computation with an outcome.* A computation
$`c` of the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] _has
an outcome_ when, from every state $`S`, $`c(S)` may end in some way: with
a result and the state after it, or in UB.

$$`\mathrm{HasOutcome}(c) \iff \forall S.\ \exists e.\ c(S) \leadsto e`

Mapping the results of $`c` keeps an outcome. A computation $`x` of the
set monad that may end in some way, run in the state layer, has an outcome
from every state, which it keeps; and when, so run, it has an outcome from
some state, $`x` may end in some way.

In a semantics of a dialect in the state layer, an op _has an outcome_ when
what it runs by its own rule has one, on every operand vector: its meaning
when it is not a terminator, its exit when it is.
:::

:::readable Fir.MemTotal Fir.LawfulDialectTotal (pin := Fir.OwnRuleHas) (fingerprint := "10655181270058211737")
*Definitions: total with memory, and a dialect lawful in its totality.* An
op $`o` is _total with memory_ when, wherever a run names the dialect's
memories, by any names $`N`, layout entries and map $`\rho` from the
dialect's memories to $`N`, what $`o` runs by its own rule has an outcome
from any memories, on every operand vector: its meaning when it is not a
terminator, its exit when it is.

A dialect is _lawful in its totality_ when every valid op instance that is
a terminator or calls no function is total with memory. The class asks for
no semantics in the set monad, so a dialect whose ops touch memory can
meet it. It is what progress with memory asks of a dialect
({ref "The-fir-specification--Memory--Progress-and-no-stuck-path___-with-memory"}[progress with memory]),
as {ref "The-fir-specification--Execution--Poison-classes"}[totality] in
the set monad is what progress asks of runs in the set monad.
:::

:::readable Fir.MemTotal.ofLifts Fir.MemTotal.setM Fir.LawfulDialectTotal.ofLawful (pin := Fir.OpTotal) (pin := Fir.OpLiftsSetM) (fingerprint := "9589096651207859662")
*Theorems: totality with memory, for an op that touches no memory.* An op
that is
{ref "The-fir-specification--Memory--Runs-with-memory"}[tied] and total
in the set monad is total with memory: its rule keeps the memories, and so
has a way to end from every memories. In a dialect that lifts the set
monad, every op is tied, and an op total with memory is total in the set
monad too. So a lawful dialect that lifts the set monad is lawful in its
totality. The dialects of the tests are; the core dialect is lawful in its
totality op by op, from each op's own tie.
:::
