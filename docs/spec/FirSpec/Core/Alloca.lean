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

:::moduleDocs (fingerprint := "17066033896169891471")
:::

:::readable Fir.Core.Ty.units Fir.Core.Ty.units?_int Fir.Core.Ty.units?_float (pin := Fir.MemLayout.bitsUnits) (pin := Fir.Core.Ty.units?) (fingerprint := "8017750107794323725")
*Definition: the units of a type.* In a memory whose
{ref "The-fir-specification--Abstract-syntax--Data-layouts"}[entry] is
$`e`, where the pointers of memory $`M` are $`p(M)` bits wide, a value of
the type $`t` takes $`\mathrm{units}_{e,p}(t)` units:

$$`\mathrm{units}_{e,p}(\mathsf{i}W) = \lceil W / u_e \rceil \qquad \mathrm{units}_{e,p}(\mathsf{ptr}\langle M \rangle) = \lceil p(M) / u_e \rceil \qquad \mathrm{units}_{e,p}(\mathsf{float}\langle e',m \rangle) = \lceil (1+e'+m) / u_e \rceil`

where $`u_e` is the entry's unit width. For an integer or a float type it
is the number of units that its
{ref "The-fir-specification--Memory--The-core___s-values-in-memory"}[encoding]
writes: a float takes the units of the integer of its width (#264).
:::

:::readable Fir.Core.Ty.naturalAlign Fir.Core.Ty.naturalAlign_int Fir.Core.Ty.naturalAlign_float (pin := Fir.MemLayout.intAlign) (fingerprint := "16595237279293571164")
*Definition: the natural alignment of a type.* The natural alignment of
the type $`t` in the memory of the entry $`e` is the least power of two
that is at least $`\mathrm{units}_{e,p}(t)`. For $`\mathsf{i}W` it is the
natural alignment that the
{ref "The-fir-specification--Abstract-syntax--Data-layouts"}[data layout]
gives the integer, as the human ruled on 2026-11-14 (#378): in memory 0,
$`\mathsf{i32}` is aligned to 4 units. For
$`\mathsf{float}\langle e',m \rangle` it is that of
$`\mathsf{i}(1+e'+m)`, the natural alignment of the float's size, as the
human ruled on 2026-11-15 (#397): in memory 0, $`\mathsf{f16}` and
$`\mathsf{bf16}` are aligned to 2 units, $`\mathsf{f32}` to 4,
$`\mathsf{f64}` to 8 and $`\mathsf{f128}` to 16.
:::

:::readable Fir.Core.Ty.defaultAlign Fir.Core.allocaShape Fir.Core.allocaRule (pin := Fir.MonadMemory) (pin := Fir.Core.Op) (fingerprint := "14773220625118106683")
*Definition: the rule of $`\mathsf{alloca}`.* Let a run's memories have
the layout entries $`\ell`, and let the run name the core's memory $`x`
as $`\rho(x)`. For $`\mathsf{alloca}_N~k~t~c~a`, which allocates $`c`
values of the type $`t` of the kind $`k` in memory $`N`, aligned to $`a`
units when $`a` is given, let $`e = \ell(\rho(N))` and
$`p(M) = \mathrm{ptr}_{\ell(\rho(M))}`, the pointer width of the entry of
memory $`M`. The allocation takes

$$`n = c \cdot \mathrm{units}_{e,p}(t) \qquad \text{units, aligned to} \qquad \begin{cases} a & \text{if } a \text{ is given} \\ \mathrm{align}_{e,p}(t) & \text{otherwise} \end{cases}`

where $`\mathrm{align}_{e,p}(t)` is the default alignment of $`t`: its
natural alignment, the least power of two that is at least
$`\mathrm{units}_{e,p}(t)`, but for $`\mathsf{ptr}\langle N \rangle`
itself the alignment that $`e` gives its pointers, the natural one unless
the entry writes $`\mathsf{align}(A)`. $`\mathrm{units}_{e,p}` counts
$`\mathsf{i}W` as its $`W` bits, $`\mathsf{float}\langle e',m \rangle` as
its $`1+e'+m` bits and $`\mathsf{ptr}\langle M \rangle` as $`p(M)` bits,
each rounded up to whole units of $`e`. In a
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

The count $`c`, and so $`n`, has no bound, as the human ruled on
2026-11-14 (#382): an allocation larger than a machine holds is a resource
error of the run, as a deep recursion is, and not a rule of the spec.
:::

:::readable Fir.Core.Ty.fieldShape_eq_allocaShape (pin := Fir.Core.Ty.fieldShape) (fingerprint := "18093245466459853265")
*Theorem: a field takes what one allocated value takes.* For every map
$`\ell` from memories to their layout entries, every memory $`n` and every
core type $`t`, an integer, a float or a pointer, the units and the alignment that a field of
type $`t` takes in an aggregate's layout of memory $`n`
({ref "The-fir-specification--Validation--Core-rules"}[the core's field shape])
are those of $`\mathsf{alloca}_n~k~t~1` with no alignment, in a run that
names each memory by itself: the units of one value of $`t` and its
default alignment. So a layout and an allocation of memory $`n` count the
same units (ADR-2026-11-16-1546).
:::
