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

:::moduleDocs (fingerprint := "15797776038052386421")
:::

:::readable Fir.Core.Ty Fir.Core.maxWidth Fir.Core.floatWidth (pin := Fir.Core.Ty.Valid) (pin := Fir.Core.Ty.decode) (fingerprint := "1975117555932158975")
*Definition: the core types.* A type of the core dialect is an integer type
$`\mathsf{i}N`, for a width $`N`, a float type
$`\mathsf{float}\langle e,m \rangle`, for an exponent width $`e` and a
mantissa width $`m`, or the type $`\mathsf{ptr}`:

```grammar Fir.Core.Ty
t
int \mathsf{i}N
float \mathsf{float}\langle e,m \rangle
ptr \mathsf{ptr}
```

The Lean writes $`\mathsf{i}N` as `int N` and
$`\mathsf{float}\langle e,m \rangle` as `float e m`. The widest integer
type has $`N_{\max} = 2^{24} - 1 = 16{,}777{,}215` bits, the limit of MLIR;
the Lean calls it `maxWidth`.

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
* $`\mathsf{ptr}` is reserved for pointers. The core dialect has no op on
  it yet, and its values wait for the memory model, which is not decided.

The grammar allows types that no program may hold. The
{ref "The-fir-specification--Validation--Core-rules"}[core rules] of
validation accept $`\mathsf{i}N` only when $`1 \le N \le N_{\max}`, so
$`\mathsf{i0}` is never a valid type, accept
$`\mathsf{float}\langle e,m \rangle` only when $`e \ge 2`, $`m \ge 1`
and $`1 + e + m \le N_{\max}`, and reject $`\mathsf{ptr}` everywhere. The
text format reads no integer type wider than $`N_{\max}`, and no float type
wider than $`N_{\max}` bits in all.

These are the types of one dialect, not the whole type system of fir: a
{ref "The-fir-specification--Abstract-syntax--Dialects"}[dialect] brings its
own types.
:::
