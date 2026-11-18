import VersoManual
import Fir.Gpu.Validation
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the rules of `gpu`, which renders
`Fir.Gpu.Validation` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The GPU dialect's rules: readable blocks" =>

:::moduleDocs (fingerprint := "13928833768383133596")
:::

:::readable Fir.Gpu.ValidTy Fir.Gpu.instDecidableValidTy (fingerprint := "4133016473030974221")
*Definition: the valid types of `gpu`.* A type is valid in `gpu` exactly
when it is a valid core type, since its types are the core's. Whether it
is valid is decided.
:::

:::readable Fir.Gpu.Op.Valid Fir.Gpu.Op.attrTypes Fir.Gpu.instDecidableOpValid (fingerprint := "6095714268801176293")
*Definition: the rule of an op of `gpu`.* A question of `gpu` is valid
when it gives an $`\mathsf{i32}`, the width of every id and size of a
work-item. An allocation has the rules of `alloca` but its kind: it
allocates at least one value, its alignment, when given, is a power of two
no larger than the data layout's limit, and its type is a valid integer or
pointer type:

$$`\frac{N = 32}{C \vdash \mathsf{query}_N~q~d~\text{valid}} \qquad \frac{1 \le c \quad (a~\text{absent or a valid alignment}) \quad t \in \{\mathsf{i}W, \mathsf{ptr}\langle m\rangle\}~\text{valid}}{C \vdash \mathsf{alloc}_n~t~c~a~\text{valid}}`

So `%i: i64 = gpu.work_item_id gpu.x` decodes, and validation rejects it.
An allocation carries its type $`t` in its attributes, and when $`t` is
valid the data layout checks the memory a pointer type there names, as for
`alloca`; its result type names the memory $`n`, which the layout checks as
it checks every type. So work-group memory is any memory that the host's
data layout declares. Whether the rule holds is decided.
:::

:::readable Fir.Gpu.instDialectValidation Fir.Gpu.instDecidableDialectValidation (fingerprint := "6830372403999317208")
*Definition: the rules of `gpu`, and their check.* `gpu` accepts the
core's valid types, its ops refer to no symbol, an allocation carries its
type, and it adds no rule for a
function, a region or an item. Its types are the core's, and each is a
field of an aggregate's layout with the units and alignment that the core
gives it. Whether a function is a kernel is where it
lives: in a device module whose dialect set names `gpu`. The dialect-set
rule already keeps every word of `gpu` out of a module whose set does not
name it. Each of these rules is decided, so the validation check runs them.
:::
