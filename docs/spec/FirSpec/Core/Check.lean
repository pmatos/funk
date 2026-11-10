import VersoManual
import Fir.Core.Check
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the core dialect's rules, decided,
which renders `Fir.Core.Check` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The core dialect's rules, decided: readable blocks" =>

:::moduleDocs (fingerprint := "2810980850477788012")
:::

:::readable Fir.Core.Rejects.deadBlock_problems (pin := Fir.Core.Ty.Valid) (pin := Fir.Core.maxWidth) (pin := Fir.Core.Op.Valid) (fingerprint := "637337370968257790")
*Theorem: the check finds a problem in the rejected function, in every
module.* For every module context $`C` and every lookup that agrees with
$`C`, the check of the function `@f` of the section on
{ref "The-fir-specification--Validation--A-rejected-function"}[a rejected function]
gives at least one problem.

It follows from two theorems: validation rejects the function, and the
check of a function decides its validity. It is a theorem about every
module that holds the function, where a test could try only some.

The check runs on core modules because the core dialect's own rules can be
decided, case by case. Whether a core
type is valid compares $`N` with 1 and $`2^{24} - 1` for $`\mathsf{i}N`,
and is false for $`\mathsf{ptr}`. Whether a core op obeys the
{ref "The-fir-specification--Validation--Core-rules"}[core rules] in an op
context compares types, widths or the symbol table's answer. So the core
dialect is a
{ref "The-fir-specification--Validation--The-validation-check"}[decidable dialect].
:::

:::readable Fir.Core.Rejects.deadModule (pin := Fir.Core.Rejects.deadBlock) (fingerprint := "13243833345381518612")
*Definition: the rejected function, alone in a module.* The module holds
the function `@f` and nothing else, and its location table has the one
entry `@0 = unknown`, which every op of `@f` refers to. A check run when
the spec is built confirms that the validation check gives it exactly one
problem: "block `^dead` is not reachable from the entry", placed at the
function `@f`, the block `^dead` and the location reference 0.
:::
