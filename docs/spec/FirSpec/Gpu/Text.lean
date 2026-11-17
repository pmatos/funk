import VersoManual
import Fir.Gpu.Text
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the text of `gpu`, which renders
`Fir.Gpu.Text` (ADR-2026-11-05-2012). Each block explains declarations of
that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "The GPU dialect in text: readable blocks" =>

:::moduleDocs (fingerprint := "4337651137589824036")
:::

:::readable Fir.Gpu.Dim.word Fir.Gpu.Dim.decode Fir.Gpu.Query.name Fir.Gpu.Query.decode (fingerprint := "10132642262867413315")
*Definition: the words of the dimensions and of the ops.* Each dimension
is written as a word of `gpu`, and each question as the name of its op:

$$`\begin{array}{ll} x & \texttt{gpu.x} \\ y & \texttt{gpu.y} \\ z & \texttt{gpu.z} \\ \mathsf{work\_item\_id} & \texttt{gpu.work\_item\_id} \\ \mathsf{work\_group\_id} & \texttt{gpu.work\_group\_id} \\ \mathsf{work\_group\_size} & \texttt{gpu.work\_group\_size} \\ \mathsf{num\_work\_groups} & \texttt{gpu.num\_work\_groups} \end{array}`

Reading goes the other way: a word in the table gives its dimension or
question, and every other word gives none.
:::

:::readable Fir.Gpu.allocName Fir.Gpu.Op.name Fir.Gpu.Op.attrs Fir.Gpu.decodeAlloc Fir.Gpu.Op.decode (fingerprint := "12023490568658626712")
*Definition: the text of an op of `gpu`.* $`\mathsf{query}_N~q~d` is
written as the name of $`q`, then the word of $`d` as its one attribute,
with its result type $`\mathsf{i}N`:
`%i: i32 = gpu.work_item_id gpu.x`. A question decodes from the name of a
question, exactly one attribute that is the word of a dimension, no
operand and one integer result of any width $`N`. Every other shape does
not decode, and is a parse error: a dimension such as `gpu.w` or a bare
`x`, no dimension or two, an operand, or a result that is not one integer.
So `gpu.barrier`, which no op names, does not decode either: M1
leaves out the ops that need other work-items (ADR-2026-11-09-1545).

$`\mathsf{alloc}_n~t~c~a` is named `gpu.work_group_alloca`, with result
type $`\mathsf{ptr}\langle n\rangle`, and its attributes are those of
`alloca` after its kind: the type $`t`, the count $`c` when it is not 1, and
`align(A)` with $`A = a` when $`a` is given, such as
`%p: ptr(3) = gpu.work_group_alloca i32 64 align(4)`. It writes no kind,
since its allocation always lives for the whole run of the kernel. It
decodes as `alloca` reads the same attributes after the kind `global`,
with no operand and one pointer result: a kind written, such as `stack`, a
count of 1, a negative count or alignment, an operand or an integer result
does not decode.
:::

:::readable Fir.Gpu.tyAttr Fir.Gpu.decodeTy Fir.Gpu.instDialectText (fingerprint := "274796703068110979")
*Definition: the types of `gpu` in text.* `gpu` has no type of its own,
so it writes and reads the core's types as the core does. With the op
text above, this is the text of `gpu` over the core.
:::
