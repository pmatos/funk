import VersoManual
import Fir.Execution.MemoryExposeLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on exposing in the state layer, which
renders `Fir.Execution.MemoryExposeLaws` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Exposing in the state layer: readable blocks" =>

:::moduleDocs (fingerprint := "8705589762971732313")
:::

:::readable Fir.ExposesNot (pin := Fir.Memory.Memory.addrOf) (fingerprint := "1474577921688200755")
*Definition: exposes nothing in a memory.* A computation $`c` of the state
layer over the set monad exposes nothing in the memory $`x` when, on each
path that ends, from $`S` to $`S'`, every allocation $`b` has the same
address in $`S'(x)` as in $`S(x)`: $`\mathrm{addr}_{S'(x)}(b) = \mathrm{addr}_{S(x)}(b)`.
A new allocation has none, as an id that $`S(x)` does not have.
:::

:::readable Fir.expose_apply Fir.expose_ub Fir.expose_ok (pin := Fir.instMonadMemoryStateT) (pin := Fir.Memory.Memories.expose) (fingerprint := "2832463624541034580")
*Theorems: how an exposure ends.* In the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] over
the set monad, the
{ref "The-fir-specification--Memory--The-memory-effect"}[memory effect]'s
exposure of $`p` in the memory $`x` ends from the memories $`S` in one of
two ways: with the integer and memories that
{ref "The-fir-specification--Memory--Address-policies"}[exposing] gives, or
in UB, for the reason that no address fits. It ends in UB exactly when the
pointer's allocation has no address and no address fits it. The memories it
ends with are $`S`, or $`S` with an allocation of $`x` that had no address
exposed.
:::

:::readable Fir.expose_hasOutcome Fir.expose_finitelyMany (pin := Fir.HasOutcome) (pin := Fir.FinitelyMany) (fingerprint := "5569169458846885717")
*Theorems: an exposure has one outcome.* From any memories an exposure has
an outcome, so it
{ref "The-fir-specification--Memory--Totality-with-memory"}[always has an outcome],
and at most one that ends, so it has
{ref "The-fir-specification--Memory--Ops-of-finitely-many-outcomes"}[finitely many].
:::

:::readable Fir.expose_writesNot Fir.expose_allocatesNot Fir.expose_exposesNot (pin := Fir.WritesNot) (pin := Fir.AllocatesNot) (fingerprint := "488109722914422118")
*Theorems: exposing changes only an address.* For every memory $`y`, $`x`
included, an exposure in $`x` meets the
{ref "The-fir-specification--Memory--Memory-obligations"}[obligations]
that it writes no unit of $`y` and neither allocates nor frees in $`y`:
every block keeps its units and its shape, and the frames are kept. For
every memory $`y \ne x`, it exposes nothing in $`y`.
:::

:::readable Fir.ReadsNot.match_ok Fir.expose_readsNot_ne (pin := Fir.ReadsNot) (pin := Fir.ReadsNot.Match) (fingerprint := "17125260846577603706")
*Theorems: an exposure reads no other memory.* Results that differ only in
the memory $`y`, as it was in one and replaced in the other, match. So for
every memory $`y \ne x`, an exposure in $`x` meets the
{ref "The-fir-specification--Memory--Memory-obligations"}[obligation] that
it does not read $`y`: replacing $`y` changes neither the integer nor
whether no address fits. It reads its own memory: the address it gives
depends on the addresses there.
:::

:::readable Fir.expose_refines (pin := Fir.StateRefinedBy) (fingerprint := "2083880051333162948")
*Theorem: exposing is monotone.* From memories that refine others, an
exposure gives the same integer and memories that refine the others', or
UB in both.
:::

:::readable Fir.alloc_exposesNot Fir.free_exposesNot Fir.load_exposesNot Fir.store_exposesNot (fingerprint := "571603311355904503")
*Theorems: the other operations expose nothing.* Allocating, freeing,
loading and storing in $`x` expose nothing in any memory, $`x` included:
every allocation keeps its address, and a new one has none.
:::
