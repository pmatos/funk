import VersoManual
import Fir.Validation.CheckExtern
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on checking external declarations,
which renders `Fir.Validation.CheckExtern` (ADR-2026-11-05-2012). Each
block explains declarations of that module and pins their fingerprint; the
build fails when the Lean changes under it.
-/

#doc (Manual) "Checking external declarations: readable blocks" =>

:::moduleDocs (fingerprint := "9864818854606624488")
:::

:::readable Fir.Extern.problem Fir.Extern.problems (pin := Fir.valueRef) (fingerprint := "13919385574555526242")
*Definition: the check of an external declaration.* A problem about the
declaration $`e` names its symbol. The check of $`e` gives, in order:

* "the parameter `%x` is not a name", for each parameter $`x` whose name
  is not a name;
* "the declaration defines `%x` more than once", for each parameter name
  that repeats one before it;
* "a type of the declaration is not valid", once, when a type that it
  states is not valid;
* "the declaration holds the attributes of its parameters or results in
  another form than the text reads", once, when they are not in the short
  form;
* "the attributes of parameter `%x` are not ones its type allows", for each
  parameter whose attributes its type's dialect does not allow;
* "the attributes of a result of the declaration are not ones its type
  allows", for each such result.

A value is spelled as the text writes it. Its parameters may end in `...`,
which the check does not report.
:::

:::readable Fir.Extern.problems_eq_nil_iff Fir.instDecidableExternValid (pin := Fir.Extern.Valid) (fingerprint := "12282693884544190565")
*Theorem: the check decides a declaration's validity.* For every dialect
whose rules are decidable and every external declaration $`e`, the check
of $`e` gives no problem exactly when $`e` is
{ref "The-fir-specification--Validation--A-function___s-signature"}[valid].
So whether a declaration is valid can be decided.
:::
