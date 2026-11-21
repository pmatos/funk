import VersoManual
import Fir.Core.LoadReads
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a load declared without a read, which renders
`Fir.Core.LoadReads` (ADR-2026-11-05-2012). Each block explains declarations of
that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "A load declared without a read: readable blocks" =>

:::moduleDocs (fingerprint := "9163177060593772845")
:::

:::readable Fir.Core.Unlawful.loadNoRead Fir.Core.Unlawful.load_typesValid (pin := Fir.Core.Op.effects) (fingerprint := "7734886575516389221")
*Definition: a declaration without a read.* The declaration gives every
core op its
{ref "The-fir-specification--Execution--Core-effects"}[effects],
but the load of an integer, $`\mathsf{load}_N~o~W~a`, only
$`\mathsf{may\text{-}ub}` and $`\mathsf{may\text{-}poison}`: it leaves
out $`\mathsf{reads}(N)`. The load of a pointer keeps its read. A load of
an $`\mathsf{i8}` through a pointer of memory 0 is a valid op instance.
:::

:::readable Fir.Core.Unlawful.oneUnit Fir.Core.Unlawful.loadShape_i8 Fir.Core.Unlawful.oneUnit_load₀ Fir.Core.Unlawful.oneUnit_load₁ (pin := Fir.Memory.Memories.load) (fingerprint := "12872963178263191196")
*Definitions and theorems: one unit of memory.* $`S_b` is the memories of
8-bit units whose memory 0 holds one live allocation of one unit, with no
address, aligned
to 1, that holds the bits $`b`. An $`\mathsf{i8}` takes one unit of the
default memory, aligned to 1, so the load of an $`\mathsf{i8}` through the
pointer to that unit gives the unit $`b`, from $`S_0` and from $`S_1`.
:::

:::readable Fir.Core.Unlawful.loadNoRead_unlawful (pin := Fir.LawfulDialectEffects) (fingerprint := "10965699435837586507")
*Theorem: the obligations reject the declaration.* Over the core's own
{ref "The-fir-specification--Memory--The-core___s-rules-with-memory"}[semantics with memory],
the declaration above is not lawful in its effects. The obligation on an
op that declares no read of memory 0 asks that replacing that memory by
one of the same allocations change nothing that the load gives. But
$`S_1` is $`S_0` with its memory replaced by one of the same allocation:
the load gives $`0` from $`S_0` and $`1` from $`S_1`, so it reads memory
0, which the declaration left out. The human asked for this proof on
2026-11-10, on #231.
:::
