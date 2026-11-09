import VersoManual
import Fir.Core.Types
import Fir.Core.Validation
import Fir.Core.Text
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on core types, which renders
`Fir.Core.Types` (ADR-2026-11-05-2012). Each block explains declarations of
that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Core types: readable blocks" =>

:::moduleDocs (fingerprint := "11942781206603878332")
:::

:::readable Fir.Core.Ty Fir.Core.maxWidth (pin := Fir.Core.Ty.Valid) (pin := Fir.Core.Ty.decode) (fingerprint := "6503499008212412967")
*Definition: the core types.* A type of the core dialect is an integer type
$`\mathsf{i}N`, for a width $`N`, or the type $`\mathsf{ptr}`:

```grammar Fir.Core.Ty
t
int \mathsf{i}N
ptr \mathsf{ptr}
```

The Lean writes $`\mathsf{i}N` as `int N`. The widest integer type has
$`N_{\max} = 2^{24} - 1 = 16{,}777{,}215` bits, the limit of MLIR; the Lean
calls it `maxWidth`.

* $`\mathsf{i}N` is the type of vectors of $`N` bits. An integer type has
  no sign: the {ref "The-fir-specification--Abstract-syntax--Core-ops"}[ops]
  say how they read the bits, as $`\mathsf{sdiv}` and
  $`\mathsf{udiv}`, or $`\mathsf{icmp}~\mathsf{slt}` and
  $`\mathsf{icmp}~\mathsf{ult}`, do, and one bit pattern is read both ways
  (ADR-2026-10-29-2007).
* $`\mathsf{ptr}` is reserved for pointers. The core dialect has no op on
  it yet, and its values wait for the memory model, which is not decided.

The grammar allows types that no program may hold. The
{ref "The-fir-specification--Validation--Core-rules"}[core rules] of
validation accept $`\mathsf{i}N` only when $`1 \le N \le N_{\max}`, so
$`\mathsf{i0}` is never a valid type, and reject $`\mathsf{ptr}`
everywhere. The text format reads no integer type wider than $`N_{\max}`.

These are the types of one dialect, not the whole type system of fir: a
{ref "The-fir-specification--Abstract-syntax--Dialects"}[dialect] brings its
own types.
:::
