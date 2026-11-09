import VersoManual
import Fir.Core.Call
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on call rules, which renders
`Fir.Core.Call` (ADR-2026-11-05-2012). Each block explains declarations of
that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Call rules: readable blocks" =>

:::moduleDocs (fingerprint := "10067100057375125948")
:::

:::readable Fir.Core.Op.callTarget? (fingerprint := "10067100057375125948")
*Definition: the function that a core op calls.*
$`\mathsf{call}~f : t^* \to r^*` calls the function with the symbol $`f`,
and no other core op calls a function:

$$`\mathrm{callee}(\mathsf{call}~f : t^* \to r^*) = f`

and $`\mathrm{callee}(o)` is none for every other op $`o`.

This is all that the core dialect says about calls. The
{ref "The-fir-specification--Execution--The-interpreter"}[interpreter] runs
the function of the module that $`\mathrm{callee}(o)` names, with the
call's operands as its arguments, and the values it returns are the call's
results; the core op semantics sends each op here, as the
{ref "The-fir-specification--Execution--Effects-and-op-semantics"}[call effect]
asks of every dialect.
:::
