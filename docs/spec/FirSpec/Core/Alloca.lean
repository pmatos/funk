import VersoManual
import Fir.Core.Alloca
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the stack allocation rules, which
renders `Fir.Core.Alloca` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Stack allocation rules: readable blocks" =>

:::moduleDocs (fingerprint := "183720006938447818")
:::

:::readable Fir.Core.Ty.units Fir.Core.Ty.units?_int (pin := Fir.MemLayout.bitsUnits) (pin := Fir.Core.Ty.units?) (fingerprint := "15487003486979289830")
*Definition: the units of a type.* In a memory whose
{ref "The-fir-specification--Abstract-syntax--Data-layouts"}[entry] is
$`e`, where the pointers of memory $`M` are $`p(M)` bits wide, a value of
the type $`t` takes $`\mathrm{units}_{e,p}(t)` units:

$$`\mathrm{units}_{e,p}(\mathsf{i}W) = \lceil W / u_e \rceil \qquad \mathrm{units}_{e,p}(\mathsf{ptr}\langle M \rangle) = \lceil p(M) / u_e \rceil \qquad \mathrm{units}_{e,p}(\mathsf{float}\langle e',m \rangle) = 0`

where $`u_e` is the entry's unit width. For an integer type it is the
number of units that its
{ref "The-fir-specification--Memory--The-core___s-values-in-memory"}[encoding]
writes. A float type has no encoding yet, and takes none.
:::

:::readable Fir.Core.Ty.naturalAlign Fir.Core.Ty.naturalAlign_int (pin := Fir.MemLayout.intAlign) (fingerprint := "5201239373346199184")
*Definition: the natural alignment of a type.* The natural alignment of
the type $`t` in the memory of the entry $`e` is the least power of two
that is at least $`\mathrm{units}_{e,p}(t)`. For $`\mathsf{i}W` it is the
natural alignment that the
{ref "The-fir-specification--Abstract-syntax--Data-layouts"}[data layout]
gives the integer, as the human ruled on 2026-11-14 (#378): in memory 0,
$`\mathsf{i32}` is aligned to 4 units.
:::

:::readable Fir.Core.allocaShape Fir.Core.allocaRule (pin := Fir.MonadMemory) (pin := Fir.Core.Op) (fingerprint := "2656346521588253133")
*Definition: the rule of $`\mathsf{alloca}`.* Let a run's memories have
the layout entries $`\ell`, and let the run name the core's memory $`x`
as $`\rho(x)`. For $`\mathsf{alloca}_N~k~t~c~a`, which allocates $`c`
values of the type $`t` of the kind $`k` in memory $`N`, aligned to $`a`
units when $`a` is given, let $`e = \ell(\rho(N))` and
$`p(M) = \mathrm{ptr}_{\ell(\rho(M))}`, the pointer width of the entry of
memory $`M`. The allocation takes

$$`n = c \cdot \mathrm{units}_{e,p}(t) \qquad \text{units, aligned to} \qquad \begin{cases} a & \text{if } a \text{ is given} \\ \mathrm{align}_{e,p}(t) & \text{otherwise} \end{cases}`

where $`\mathrm{align}_{e,p}(t)` is the natural alignment of $`t`. In a
monad with the
{ref "The-fir-specification--Memory--The-memory-effect"}[memory effect],
the rule of $`\mathsf{alloca}_N~k~t~c~a` takes no operands, allocates $`n`
units of the kind $`k` with that alignment in the memory $`\rho(N)`, and
gives the pointer to the allocation as its one result. So
$`\mathsf{alloca}~\mathsf{stack}~\mathsf{i32}~4` allocates 16 units of
memory 0 aligned to 4, and
$`\mathsf{alloca}~\mathsf{stack}~\mathsf{i8}~12~\mathsf{align}(4)`
allocates 12 aligned to 4.

The pointer has provenance for the new allocation, at offset 0, and its
units are poison. A stack allocation is recorded in the innermost frame,
which frees it when its call returns
({ref "The-fir-specification--Memory--The-memories-of-a-run"}[the memories of a run]).
:::
