import VersoManual
import Fir.Execution.MemoryPoison
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on poison obligations with memory, which
renders `Fir.Execution.MemoryPoison` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Poison obligations with memory: readable blocks" =>

:::moduleDocs (fingerprint := "5466025618371562006")
:::

:::readable Fir.MemPoisonOut Fir.MemUBByOwnRules Fir.MemPropagatesPoison (pin := Fir.HVector.IsFilledBy) (pin := Fir.HVector.Any) (pin := Fir.HVector.All) (fingerprint := "14323327561986073065")
*Definitions: an op that propagates poison, with memory.* Wherever a run
names the dialect's memories, by any names $`N`, layout entries and map
$`\rho` from the dialect's memories to $`N`, the op $`o` that is not a
terminator has two clauses, over its
{ref "The-fir-specification--Memory--Memory-obligations"}[semantics with memory]
$`⟦o⟧_\rho`:

* _Poison out, with memory_: from any memories $`S`, on operands
  $`\vec{a}` of which one is poison, every result vector it returns is all
  poison.

  $$`\mathrm{Any}_{\mathrm{poison}}(\vec{a}) \land ⟦o⟧_\rho(\vec{a})(S) \leadsto \mathsf{ok}(\vec{r}, S') \implies \mathrm{All}_{\mathrm{poison}}(\vec{r})`
* _UB only by its own rules, with memory_: if it may hit UB from the
  memories $`S` on operands $`\vec{a}` of which one is poison, then it may
  hit UB from the same $`S` on some operands $`\vec{a}'` that
  {ref "The-fir-specification--Execution--Poison-classes"}[fill]
  $`\vec{a}`, replacing each poison by a defined value.

  $$`\mathrm{Any}_{\mathrm{poison}}(\vec{a}) \land ⟦o⟧_\rho(\vec{a})(S) \leadsto \mathsf{ub}(r) \implies \exists \vec{a}'.\ \vec{a} \sqsubseteq_{\mathrm{fill}} \vec{a}' \land \exists r'.\ ⟦o⟧_\rho(\vec{a}')(S) \leadsto \mathsf{ub}(r')`

The memories stay the same, since UB may depend on them: a load through a
poison pointer may be UB because some pointer in its place faults on those
memories. An op _propagates poison with memory_ when both clauses hold.
:::

:::readable Fir.MemReturnsOnDefined Fir.LawfulDialectMemPoison Fir.LawfulDialectMem (pin := Fir.TypesValid) (pin := Fir.Memory.Memories) (fingerprint := "8888602367402709010")
*Definitions: a result on defined operands with memory, and a dialect lawful
in its poison with memory.* An op _returns a result on defined operands
with memory_ when, wherever a run names the dialect's memories, it returns
a result on some operand vector with no poison, from some memories inside a
call: memories with a frame, as a run's are wherever an op runs. A load
does so from memories that hold its allocation. Memories outside every call
would not do: an op that returns only there is UB wherever a run reaches
it, as an op that is always UB is.

A dialect is _lawful in its poison with memory_ when a poison value of a
valid type is refined by every value of its type, and every valid op
instance whose poison class is _propagates_ propagates poison with memory
and returns a result on defined operands with memory. The class asks for no
semantics in the set monad, so a dialect whose ops touch memory can meet
it. A dialect is _lawful with memory_ when it is lawful in its poison with
memory,
{ref "The-fir-specification--Memory--Totality-with-memory"}[lawful in its totality]
and {ref "The-fir-specification--Memory--Monotonicity-with-memory"}[lawful in its monotonicity]:
it then holds every poison obligation over the semantics with memory, as
{ref "The-fir-specification--Execution--Poison-classes"}[lawful]
holds them in the set monad.
:::

:::readable Fir.MemPropagatesPoison.ofLifts Fir.MemPropagatesPoison.setM Fir.MemReturnsOnDefined.ofLifts Fir.MemReturnsOnDefined.setM (pin := Fir.PropagatesPoison) (pin := Fir.ReturnsOnDefined) (fingerprint := "13077384238043551035")
*Theorems: the poison obligations with memory, for a dialect that lifts the
set monad.* In a dialect that
{ref "The-fir-specification--Memory--Runs-with-memory"}[lifts the set monad],
as every dialect whose ops touch no memory does, an op propagates poison
with memory exactly when it propagates poison in the set monad, and returns
a result on defined operands with memory exactly when it does in the set
monad. Its semantics with memory runs its rule in the set monad and keeps
the memories, so a result, UB and the operands that fill a poison are the
same from every memories.
:::

:::readable Fir.LawfulDialectMemPoison.ofLawful Fir.LawfulDialectPoison.ofMem Fir.LawfulDialectPoison.iff_mem (pin := Fir.LawfulDialectPoison) (fingerprint := "11942904318688002526")
*Theorems: lawful with memory, for a dialect that lifts the set monad.* A
lawful dialect that lifts the set monad is lawful in its poison with
memory. The other way, a dialect that lifts the set monad and is lawful in
its poison, its totality and its monotonicity with memory is lawful. So, for
such a dialect, the poison obligations hold exactly when it is lawful with
memory, and the obligations with memory reject every semantics
that the poison obligations reject. The core dialect and the dialects of
the tests meet them.
:::
