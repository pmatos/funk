import VersoManual
import Fir.Core.PtrInt
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the rules of pointers as integers, which
renders `Fir.Core.PtrInt` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Rules of pointers as integers: readable blocks" =>

:::moduleDocs (fingerprint := "13580712945572408298")
:::

:::readable Fir.Core.poisonExposePointer Fir.Core.ptrExposeRule (pin := Fir.MonadMemory) (pin := Fir.MonadUB) (pin := Fir.RunItems) (fingerprint := "1911466079812049626")
*Definition: the rule of $`\mathsf{ptr\_expose}`.* Let a run's memories
have the layout entries $`\ell`, let the run name the core's memory $`x` as
$`\rho(x)` and give the items $`L`. For $`\mathsf{ptrExpose}~N~W` on the
pointer $`p`:

* if $`p` is poison, immediate UB, for the reason "a ptr\_expose of a
  poison pointer";
* otherwise the memory effect's exposure of $`p` in $`\rho(N)` under the
  run's address policy $`L.\mathrm{addrs}(N)`, at the pointer width
  $`P = \ell(\rho(N)).\mathrm{pointer}`: the allocation's address plus the
  offset of $`p`, modulo $`2^P`, cut or padded to $`W` bits. It is UB when
  no address may be given.

A valid module has $`W = P`, so the cut and the padding only make the rule
total for a module that `fir-ref run` runs without validating it.
:::

:::readable Fir.Core.ptrFromIntRule (pin := Fir.MonadMemory) (pin := Fir.RunItems) (fingerprint := "2277570268470996773")
*Definition: the rule of $`\mathsf{ptr\_from\_int}`.* For
$`\mathsf{ptrFromInt}~N~W` on the integer $`i`, with $`P` as above: when
$`i` is defined, the pointer that the memory effect turns $`i`, cut or
padded to $`P` bits, back into in $`\rho(N)` under the run's resolver
$`L.\mathrm{resolvers}(N)`: a pointer into a live, exposed allocation that
holds the address, the end included, or a pointer with no provenance. When
$`i` is poison, the result is poison, and the call still counts, with the
address $`0`, which no allocation holds: memories that refine each other
then keep equal counts.
:::

:::readable Fir.Core.ptrExposeRule_map Fir.Core.ptrFromIntRule_map (pin := Fir.MonadMorphism) (fingerprint := "9314055711888221490")
*Theorems: a morphism maps the rules.* A monad morphism that keeps UB and
exposing maps the rule of $`\mathsf{ptr\_expose}` in the one monad to the
same rule in the other, and one that keeps turning integers back into
pointers maps the rule of $`\mathsf{ptr\_from\_int}`, on every operand.
:::
