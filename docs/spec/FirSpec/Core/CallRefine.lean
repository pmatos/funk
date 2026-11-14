import VersoManual
import Fir.Core.CallRefine
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on refinement through core calls, which
renders `Fir.Core.CallRefine` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Refinement through core calls: readable blocks" =>

:::moduleDocs (fingerprint := "17626712809999231749")
:::

:::readable Fir.Core.Op.monotone_all Fir.Core.opsMonotone_all (fingerprint := "17589815968064864618")
*Theorems: every core op that runs by its own rule is monotone, and so
every core function has monotone ops.* For every
{ref "The-fir-specification--Abstract-syntax--Core-ops"}[core op] $`o`,
at every width, if $`o` is a terminator or has no callee, then $`o` is
{ref "The-fir-specification--Execution--Poison-classes"}[monotone]. That
is every core op but $`\mathsf{call}`, and each is monotone by the
obligation that its family proves. So every core function, valid or not,
has
{ref "The-fir-specification--Execution--Returns-and-UB___-followed-back"}[monotone ops],
which is what the general refinement theorems ask.

The width $`0` is included, which validation rejects. So refined arguments
with memory hold for every core module, valid or not, where the
{ref "The-fir-specification--Execution--What-the-lawful-class-gives"}[lawful class]
would give them only for valid modules. Congruence in the callee with memory
goes through the lawful class, so it asks for a valid module.
:::

:::readable Fir.Core.Ty.Finite Fir.Core.Ty.values Fir.Core.Ty.mem_values Fir.Core.argVectors Fir.Core.mem_argVectors (pin := Fir.ChoiceTree.allBits) (pin := Fir.Core.Ty.toType) (pin := Fir.Core.floatWidth) (fingerprint := "1998525394283694137")
*Definitions and theorems: every value of a core type with finitely many
values, and every argument vector.* An integer and a float type have
finitely many values; a pointer type has infinitely many, one for every
allocation and offset. The values of a
{ref "The-fir-specification--Execution--Core-values"}[core type] with
finitely many values are listed:

* the values of $`\mathsf{i}N` are poison and the $`2^N` vectors of $`N`
  bits, in order from $`0` to $`2^N - 1`;
* the values of $`\mathsf{float}\langle e,m \rangle` are poison and the
  vectors of $`1 + e + m` bits, in the same order.

No list holds the values of $`\mathsf{ptr}\langle N \rangle`, so the
list takes the proof that its type has finitely many values. The argument
vectors of a list of types $`t_1, \dots, t_n` are
listed too: every choice of a value of $`t_1`, then of $`t_2`, up to
$`t_n`, and the one empty vector when $`n = 0`.

*Theorems:* every value of a core type $`t` with finitely many values is
in the list of values of $`t`, and when each of the types $`t^*` has
finitely many values, every vector of values of $`t^*` is in the list of
argument vectors of $`t^*`. So the parameter types of a core function with
no pointer parameter have finitely many argument vectors, which
{ref "The-fir-specification--Memory--Congruence-in-a-core-callee"}[congruence in a core callee]
asks of its form with memory.
:::
