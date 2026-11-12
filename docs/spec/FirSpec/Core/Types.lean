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

:::moduleDocs (fingerprint := "15458445134579424081")
:::

:::readable Fir.Core.Ty Fir.Core.maxWidth Fir.Core.maxMemory Fir.Core.floatWidth (pin := Fir.Core.Ty.Valid) (pin := Fir.Core.Ty.decode) (fingerprint := "17770481132875150779")
*Definition: the core types.* A type of the core dialect is an integer type
$`\mathsf{i}N`, for a width $`N`, a float type
$`\mathsf{float}\langle e,m \rangle`, for an exponent width $`e` and a
mantissa width $`m`, or a pointer type $`\mathsf{ptr}\langle N \rangle`,
for a memory $`N`:

```grammar Fir.Core.Ty
t
int \mathsf{i}N
float \mathsf{float}\langle e,m \rangle
ptr \mathsf{ptr}\langle N \rangle
```

The Lean writes $`\mathsf{i}N` as `int N`,
$`\mathsf{float}\langle e,m \rangle` as `float e m` and
$`\mathsf{ptr}\langle N \rangle` as `ptr N`. The widest integer
type has $`N_{\max} = 2^{24} - 1 = 16{,}777{,}215` bits, the limit of MLIR;
the Lean calls it `maxWidth`. The highest memory a pointer type names is
$`2^{24} - 1` too, as LLVM bounds its address spaces; the Lean calls it
`maxMemory`.

* $`\mathsf{i}N` is the type of vectors of $`N` bits. An integer type has
  no sign: the {ref "The-fir-specification--Abstract-syntax--Core-ops"}[ops]
  say how they read the bits, as $`\mathsf{sdiv}` and
  $`\mathsf{udiv}`, or $`\mathsf{icmp}~\mathsf{slt}` and
  $`\mathsf{icmp}~\mathsf{ult}`, do, and one bit pattern is read both ways
  (ADR-2026-10-29-2007).
* $`\mathsf{float}\langle e,m \rangle` is the IEEE 754 binary format with
  $`e` exponent bits and $`m` explicit mantissa bits. A value of it is
  $`1 + e + m` bits, the Lean's `floatWidth e m`: a sign bit, then the
  exponent, then the mantissa (ADR-2026-11-09-1549). Five formats have
  names of their own: $`\mathsf{f16}`, $`\mathsf{bf16}`, $`\mathsf{f32}`,
  $`\mathsf{f64}` and $`\mathsf{f128}` are
  $`\mathsf{float}\langle 5,10 \rangle`,
  $`\mathsf{float}\langle 8,7 \rangle`,
  $`\mathsf{float}\langle 8,23 \rangle`,
  $`\mathsf{float}\langle 11,52 \rangle` and
  $`\mathsf{float}\langle 15,112 \rangle`.
* $`\mathsf{ptr}\langle N \rangle` is the type of pointers into the
  memory $`N` (ADR-2026-11-09-1542). $`\mathsf{ptr}`, the core's pointer,
  is $`\mathsf{ptr}\langle 0 \rangle`, the pointer of the default memory,
  which every module has. A pointer of one memory is never a pointer of
  another: $`\mathsf{ptr}\langle 0 \rangle` and
  $`\mathsf{ptr}\langle 1 \rangle` are different types.

The grammar allows types that no program may hold. The
{ref "The-fir-specification--Validation--Core-rules"}[core rules] of
validation accept $`\mathsf{i}N` only when $`1 \le N \le N_{\max}`, so
$`\mathsf{i0}` is never a valid type, accept
$`\mathsf{float}\langle e,m \rangle` only when $`e \ge 2`, $`m \ge 1`
and $`1 + e + m \le N_{\max}`, and accept
$`\mathsf{ptr}\langle N \rangle` for every memory number up to
`maxMemory`; the module's
{ref "The-fir-specification--Abstract-syntax--Data-layouts"}[data layout]
says which memories the module has.
The text format reads no integer type wider than $`N_{\max}`, no float type
wider than $`N_{\max}` bits in all, and no pointer type of a memory above
`maxMemory`.

These are the types of one dialect, not the whole type system of fir: a
{ref "The-fir-specification--Abstract-syntax--Dialects"}[dialect] brings its
own types.
:::
