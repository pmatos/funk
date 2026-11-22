import VersoManual
import Fir.Syntax.Aggregate
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on aggregates' layouts, which renders
`Fir.Syntax.Aggregate` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Aggregates' layouts: readable blocks" =>

:::moduleDocs (fingerprint := "1079449942917164172")
:::

:::readable Fir.Field Fir.Aggregate Fir.Aggregate.types Fir.Aggregate.limit Fir.Aggregate.InLimits (fingerprint := "7485320805007985135")
*Definition: an aggregate's layout.* In M1 an aggregate is a layout over
memory, not a value (ADR-2026-11-09-1550). A layout is an item of the
core's kind `aggregate` (ADR-2026-11-16-1546): the memory it describes, by
its number, a size and an alignment, and a list of fields, all counted in
the units of that memory:

```grammar Fir.Field
\mathit{field}
offset,ty,count \{\mathsf{offset}~o,~\mathsf{ty}~t,~\mathsf{count}~c^?\,\}
```

```grammar Fir.Aggregate
\mathit{aggregate}
name,mem,size,align,fields \begin{array}{l} \{\mathsf{name}~s,~\mathsf{mem}~n, \\ \enspace \mathsf{size}~z,~\mathsf{align}~a, \\ \enspace \mathsf{fields}~\mathit{field}^*\,\} \end{array}
```

A field is one value of the scalar type $`t` at the offset $`o`, or, when it
has a count $`c`, a repeated field: an array of $`c` elements of $`t`. Each
element is rounded up to the alignment of $`t` (the human's ruling of
2026-11-16 on #236), so four `i24` in memory 0 take 16 units, not 12. In
text a layout is written `aggregate @s() memory(n) size(z) align(a)`, then
`field(o, t)` or `field(o, t, c)` for each field, then `{` and `}` on the
next line. $`\mathrm{types}(A)` is the types it states, one for each field.
Every number of a layout is at most $`2^{64} - 1`, its limit; a layout
whose numbers are all within it is within its limits, and only such a
layout can be written.
:::

:::readable Fir.InitPiece.InLimits Fir.Global.InLimits (fingerprint := "13179149203291508932")
*Definition: a global within its limits.* The numbers of a
{ref "The-fir-specification--Abstract-syntax--Globals"}[global] are within
its limits when its memory, size and alignment, each count of zeros and
each offset of an address are at most $`2^{64} - 1`, an aggregate's limit.
A unit has no limit here: validation bounds it by its memory's unit width.
:::
