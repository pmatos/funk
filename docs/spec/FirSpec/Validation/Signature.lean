import VersoManual
import Fir.Validation.Signature
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a function's signature, which
renders `Fir.Validation.Signature` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "A function's signature: readable blocks" =>

:::moduleDocs (fingerprint := "9109870626370042610")
:::

:::readable Fir.Func.SigValid (pin := Fir.AttrsTrimmed) (pin := Fir.Func.paramAttrsAll) (pin := Fir.Func.resultAttrsAll) (fingerprint := "17308138750463034735")
*Definition: a valid signature.* For every dialect with
{ref "The-fir-specification--Validation--Scope-and-symbols"}[validation rules],
the signature of a function $`f` is valid when:

* its parameters do not end in `...`: defining a variadic function stays out
  of M1, and only an external declaration may be variadic;
* $`f` holds the attributes of its parameters, and of its results, as at
  most one list per place, with no empty list at the end, the form that
  decoding the text gives;
* for each parameter $`x : t` with attributes $`A`, and each result $`t`
  with attributes $`A`, the dialect allows $`A` after $`t`:
  $`\mathrm{validSigAttrs}(t, A)`.

A dialect allows no attribute by default. The core allows one word, `sext`
or `zext`, after an integer type narrower than 32 bits.
:::
