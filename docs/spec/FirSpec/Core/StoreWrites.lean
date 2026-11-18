import VersoManual
import Fir.Core.StoreWrites
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a store declared without a write,
which renders `Fir.Core.StoreWrites` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "A store declared without a write: readable blocks" =>

:::moduleDocs (fingerprint := "6404569940324015037")
:::

:::readable Fir.Core.Unlawful.storeNoWrite Fir.Core.Unlawful.store_typesValid (pin := Fir.Core.Op.effects) (fingerprint := "17259705421009178995")
*Definition: a declaration without a write.* The declaration gives every
core op its
{ref "The-fir-specification--Execution--Core-effects"}[effects],
but the store of an integer, $`\mathsf{store}_N~o~W~a`, only
$`\mathsf{may\text{-}ub}`: it leaves out $`\mathsf{writes}(N)`. The store
of a pointer keeps its write. A store of an $`\mathsf{i8}` through a
pointer of memory 0 is a valid op instance.
:::

:::readable Fir.Core.Unlawful.storeAlign_i8 Fir.Core.Unlawful.oneUnit_store (pin := Fir.Memory.Memories.store) (pin := Fir.Core.Unlawful.oneUnit) (fingerprint := "499630171697357063")
*Theorems: a store of one unit.* An $`\mathsf{i8}` is stored to the
default memory aligned to 1, so the store of the $`\mathsf{i8}` 1 through
the pointer to the one unit of $`S_0`, the memories of the section on a
load declared without a read whose one allocation holds 0, gives $`S_1`,
the same memories with that unit holding 1.
:::

:::readable Fir.Core.Unlawful.storeNoWrite_unlawful (pin := Fir.LawfulDialectEffects) (fingerprint := "11489798942298084601")
*Theorem: the obligations reject the declaration.* Over the core's own
{ref "The-fir-specification--Memory--The-core___s-rules-with-memory"}[semantics with memory],
the declaration above is not lawful in its effects. The obligation on an
op that declares no write of memory 0 asks that every path that ends keep
the units that memory 0 held. But the store from $`S_0` ends in $`S_1`,
whose one unit holds 1 where $`S_0`'s held 0, so it writes memory 0, which
the declaration left out. This is the counterpart for stores of the
rejection of a load declared without a read, which the human asked for on
2026-11-10, on #231.
:::
