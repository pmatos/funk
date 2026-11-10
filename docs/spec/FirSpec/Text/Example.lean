import VersoManual
import Fir.Text.Example
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the example, which renders
`Fir.Text.Example` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Example: readable blocks" =>

:::moduleDocs (fingerprint := "3180108140818141476")
:::

:::readable Fir.Example.sum Fir.Example.sum10 Fir.Example.sumModule (fingerprint := "3180108140818141476")
*Definition: the example module.* The module above, as
{ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[abstract syntax]:
the function `@sum`, the function `@sum10` and the location table with the
seven entries `@0` to `@6`. Each op of the text is one op of the abstract
syntax, with the same results, op instance, operands, successors and
location reference. For example, the line

```
  %acc1: i32 = add nsw %acc, %i @3
```

is the op with the one result $`\mathit{acc1} : \mathsf{i32}`, the op
instance $`\mathsf{add}_{32}~\mathsf{nsw}`, the operands $`\mathit{acc}`
and $`i`, no successors, no regions and the location reference 3; and

```
  cond_br %done, ^exit(%acc), ^body @2
```

is $`\mathsf{cond\_br}` with the operand $`\mathit{done}`, the successors
`^exit(%acc)` and `^body`, and the location reference 2.

Checks run on every build: that the module prints as the text above, byte
for byte, and that the parser reads that text back to a module that prints
as the same text.
:::
