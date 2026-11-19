import VersoManual
import Fir.Core.PtrAccess
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the pointer load and store rules,
which renders `Fir.Core.PtrAccess` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Pointer load and store rules: readable blocks" =>

:::moduleDocs (fingerprint := "7669508355646177871")
:::

:::readable Fir.Core.ptrShape Fir.Core.ptrShape_fst (pin := Fir.Core.allocaShape) (pin := Fir.Core.Ty.defaultAlign) (fingerprint := "9600153020248372393")
*Definition: the shape of a pointer access.* An access of a value of
$`\mathsf{ptr}\langle M \rangle` in the memory $`N`, with the alignment
$`a` when the op gives one, takes the units and the alignment of an
$`\mathsf{alloca}` of one $`\mathsf{ptr}\langle M \rangle` in memory $`N`:

$$`\lceil p_M / u_N \rceil \qquad \text{units, as an access aligned to} \qquad \begin{cases} a & \text{if } a \text{ is given} \\ \mathrm{align}_N(\mathsf{ptr}\langle M \rangle) & \text{otherwise} \end{cases}`

where $`p_M` is the pointer width of memory $`M`'s entry, $`u_N` the unit
width of memory $`N`'s, and $`\mathrm{align}_N(\mathsf{ptr}\langle M \rangle)`
the default alignment of the
{ref "The-fir-specification--Memory--Stack-allocation-rules"}[stack allocation rules]:
the least power of two that is at least those units, but in memory $`M`
itself the alignment that $`M`'s entry gives its pointers. The alignment
does not change the number of units. In memory 0 a pointer of memory 0
takes 8 units aligned to 8.
:::

:::readable Fir.Core.loadPtrResult Fir.Core.storePtrUnits Fir.Core.loadPtrRule Fir.Core.storePtrRule (pin := Fir.MonadMemory) (pin := Fir.MonadUB) (pin := Fir.Memory.decodePtr) (pin := Fir.Memory.encodePtr) (pin := Fir.Core.Op) (fingerprint := "2717633480245080910")
*Definition: the rules of the load and store of a pointer.* Let a run's
memories have the layout entries $`\ell`, and let the run name the core's
memory $`x` as $`\rho(x)`. For $`\mathsf{load}_N~o~\mathsf{ptr}\langle M \rangle~a`
on the pointer $`p`, and $`\mathsf{store}_N~o~\mathsf{ptr}\langle M \rangle~a`
on the value $`v` and the pointer $`p`, let $`e = \ell(\rho(N))` and $`k`
the units of the shape of a pointer access. In a monad with UB and the
{ref "The-fir-specification--Memory--The-memory-effect"}[memory effect]:

* if $`p` is poison, each rule is immediate UB, for the reason of
  $`\mathsf{load}` or $`\mathsf{store}`;
* otherwise the load is the
  {ref "The-fir-specification--Memory--The-memory-model"}[aligned load]
  through $`p`, from $`\rho(N)`, of $`k` units at the access's alignment,
  {ref "The-fir-specification--Memory--Values-in-units"}[decoded] in the
  byte order of $`e` as a pointer of memory $`M`: the pointer $`q` when the
  units are the $`k` fragments of $`q` with the memory $`M`, in order, and
  poison otherwise;
* and the store is the aligned store through $`p`, to $`\rho(N)`, of the
  encoding of $`v` in $`k` units: the fragments of $`v` with the memory
  $`M`, in the byte order of $`e`, or $`k` poison units when $`v` is poison.
  It gives no result.

An access that faults is UB for the reason of its fault. So a pointer
stored and loaded back is the same pointer, its provenance and offset
kept, while fresh memory, units of bits, the fragments of a pointer of
another memory and a pointer partly overwritten all load as poison (the
human's rulings of 2026-11-11 on #231, Q3). The ordering $`o` does not
change the rules: validation accepts only $`\mathsf{nonatomic}`.
:::
