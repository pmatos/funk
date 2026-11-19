import VersoManual
import Fir.Core.Load
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the load rules, which renders
`Fir.Core.Load` (ADR-2026-11-05-2012). Each block explains declarations of
that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Load rules: readable blocks" =>

:::moduleDocs (fingerprint := "3722738444429852241")
:::

:::readable Fir.Core.loadShape (pin := Fir.MemLayout.bitsUnits) (pin := Fir.MemLayout.intAlign) (fingerprint := "6193383421806179696")
*Definition: the shape of a load.* A load of $`\mathsf{i}W` from a memory
whose
{ref "The-fir-specification--Abstract-syntax--Data-layouts"}[entry] is
$`e`, with the alignment $`a` when the op gives one, reads

$$`\lceil W / u_e \rceil \qquad \text{units, as an access aligned to} \qquad \begin{cases} a & \text{if } a \text{ is given} \\ \mathrm{align}_e(\mathsf{i}W) & \text{otherwise} \end{cases}`

where $`u_e` is the entry's unit width and $`\mathrm{align}_e(\mathsf{i}W)`
the natural alignment of $`\mathsf{i}W` in that memory, the least power of
two that is at least its units. In memory 0, an $`\mathsf{i32}` takes 4
units aligned to 4, and an $`\mathsf{i1}` one unit aligned to 1.
:::

:::readable Fir.Core.poisonPointer Fir.Core.loadResult Fir.Core.loadRule (pin := Fir.MonadMemory) (pin := Fir.MonadUB) (pin := Fir.Memory.decodeInt) (pin := Fir.Core.Op) (fingerprint := "13757023457367892234")
*Definition: the rule of $`\mathsf{load}`.* Let a run's memories have the
layout entries $`\ell`, and let the run name the core's memory $`x` as
$`\rho(x)`. For $`\mathsf{load}_N~o~W~a` on the pointer operand $`p`, let
$`e = \ell(\rho(N))`. In a monad with UB and the
{ref "The-fir-specification--Memory--The-memory-effect"}[memory effect]:

* if $`p` is poison, the rule is immediate UB, for the reason "a load
  through a poison pointer": some defined pointer in its place faults, as
  one with no provenance does;
* otherwise it is the
  {ref "The-fir-specification--Memory--The-memory-model"}[aligned load]
  through $`p`, from the memory $`\rho(N)`, of the units of $`\mathsf{i}W`
  at its alignment, as the shape of a load gives them. An access that
  faults is UB for the reason of its fault: no provenance, freed, out of
  bounds or misaligned, in that order. The units it loads are
  {ref "The-fir-specification--Memory--Values-in-units"}[decoded] as a
  value of $`\mathsf{i}W` in the byte order of $`e`, which is the one
  result $`[v]`.

Decoding ignores the bits past $`W` in the last unit, so an
$`\mathsf{i1}` loaded from `0xFF` is 1, and gives poison when a unit is
poison or a pointer's fragment: fresh memory reads poison, and so does a
punned load of a pointer (the human's rulings of 2026-11-11 on #231). The
ordering $`o` does not change the rule: validation accepts only
$`\mathsf{nonatomic}`.
:::
