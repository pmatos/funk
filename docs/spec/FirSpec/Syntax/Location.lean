import VersoManual
import Fir.Syntax.Location
import Fir.Validation.Rules
import Fir.Text.Print
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on locations, which renders
`Fir.Syntax.Location` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Locations: readable blocks" =>

:::readable Fir.LocRef (fingerprint := "11401156343561318334")
*Definition: a location reference.* A location reference $`r` is a natural
number, written $`\mathtt{@}r` in text. It is a key of the module's location
table, defined below, which gives the location that $`r` stands for.

An op holds a reference rather than a location, so ops that share a location
share one entry of the table, and each op's line of text stays short. The
numbers are the producer's: they are stored and printed as given, never
renumbered, so a round trip through the text gives the same numbers back.
:::

:::readable Fir.Location (pin := Fir.Location.print) (fingerprint := "15186028142405769751")
*Definition: a location.* A location says where an op came from. It is one
of six kinds:

```grammar Fir.Location
\mathit{loc}
unknown  \mathsf{unknown}
range    \mathsf{range}~\mathit{file}~l_1~c_1~l_2~c_2
name     \mathsf{name}~n
callsite \mathsf{callsite}~r_1~r_2
fused    \mathsf{fused}~r^*
derived  \mathsf{derived}~r
```

Here $`\mathit{file}` and $`n` are strings, $`l_1, c_1, l_2, c_2` natural
numbers, and each $`r` a location reference.

* $`\mathsf{unknown}`: nothing is known about where the op came from.
* $`\mathsf{range}~\mathit{file}~l_1~c_1~l_2~c_2`: a range of the source
  text of $`\mathit{file}`, from line $`l_1`, column $`c_1` to line
  $`l_2`, column $`c_2`, as MLIR writes it. Lines count from 1. Columns
  count bytes of UTF-8 from 1, and column 0 means that the column is
  unknown. The end is the position just after the range's last byte, so a
  range whose end is its start is empty.
* $`\mathsf{name}~n`: a name, such as the source variable that the op
  computes.
* $`\mathsf{callsite}~r_1~r_2`: the op came from inlining. $`r_1` is its
  location in the inlined function, and $`r_2` the location of the call.
* $`\mathsf{fused}~r^*`: the op stands for several ops, such as the result
  of merging them, and $`r^*` are their locations.
* $`\mathsf{derived}~r`: a transformation made the op from the op at $`r`,
  as when a pass expands one op into several.

The last three are built from other entries of the table, by reference. In
text, the six are written `unknown`, `"file":l:c to l:c`, `name("n")`,
`callsite(@r at @r)`, `fused(@r, …)` and `derived(@r)`.

Every op has a location, so that diagnostics can point at the source and a
frontend can map compiled code back to it; a field that may be missing is
easy to drop by accident in a pass (ADR-2026-10-29-2013). Locations never
change what a program means: no rule of execution reads them.
:::

:::readable Fir.LocTable (pin := Fir.LocTable.Valid) (pin := Fir.Location.WellFormed) (fingerprint := "9976675594473860050")
*Definition: a location table.* A module's location table is a sequence of
entries $`(r = \mathit{loc})^*`, each a location reference $`r` and the
location $`\mathit{loc}` it stands for. In text it is the block
`locs { @r = loc … }` that ends the module.

The table is a plain sequence; validation asks more of it
({ref "The-fir-specification--Validation--The-general-rules"}[the general rules]):

* the references of the entries strictly increase, so each is a key of one
  entry, and one table has one spelling;
* a location built from others refers only to keys of entries before its
  own, so no location refers to itself, directly or not;
* a $`\mathsf{fused}` location fuses at least two;
* a $`\mathsf{range}` starts at line 1 or later and does not end before it
  starts: it ends on a later line, or on the same line with an end column
  at least its start column when both columns are known (not 0);
* every reference, line and column is below the limit defined next.
:::

:::readable Fir.Location.refs Fir.Location.numbers Fir.Location.limit Fir.LocTable.InLimits (pin := Fir.LocTable.Valid) (fingerprint := "13134142017632528915")
*Definition: the numbers of a location, and their limit.* The references
that a location is built from, $`\mathrm{refs}(\mathit{loc})`, and the
numbers that it holds, $`\mathrm{nums}(\mathit{loc})`, are these sequences
($`\epsilon` is the empty sequence):

$$`\begin{aligned} \mathrm{refs}(\mathsf{callsite}~r_1~r_2) &= r_1~r_2 \\ \mathrm{refs}(\mathsf{fused}~r^*) &= r^* \\ \mathrm{refs}(\mathsf{derived}~r) &= r \\ \mathrm{refs}(\mathit{loc}) &= \epsilon \quad \text{otherwise} \end{aligned}`

$$`\begin{aligned} & \mathrm{nums}(\mathsf{range}~\mathit{file}~l_1~c_1~l_2~c_2) \\ & \quad = l_1~c_1~l_2~c_2 \\ & \mathrm{nums}(\mathit{loc}) = \mathrm{refs}(\mathit{loc}) \quad \text{otherwise} \end{aligned}`

A table $`T` is _within limits_ when every key, and every number of every
location, is below $`2^{32}`:

$$`\begin{aligned} \forall (r = \mathit{loc}) \in T.\ & r < 2^{32} \\ \wedge\ & \forall n \in \mathrm{nums}(\mathit{loc}).\ n < 2^{32} \end{aligned}`

The Lean spells $`\mathrm{nums}` `numbers`, and calls the limit
`Location.limit` and the condition `InLimits`. The limit lets every
implementation hold references, lines and columns in 32 bits, as MLIR does
(ADR-2026-11-03-1000). Validation rejects a table that is not within
limits, and checks with $`\mathrm{refs}` that each location refers only to
earlier entries.
:::
