import VersoManual
import Fir.Execution.TraceStepPaths
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a traced run of ops, one step at a time, which renders
`Fir.Execution.TraceStepPaths` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "A traced run of ops, one step at a time: readable blocks" =>

:::moduleDocs (fingerprint := "988850153275118531")
:::

:::readable Fir.Func.tStepPath_iff (pin := Fir.Func.TStepPath) (fingerprint := "15361096986935972223")
*Definition and theorem: the ways a step goes on.* A path of the traced run
of $`o :: os` with $`n + 1` steps, from $`s`, that is not stuck goes on in
one of ten ways, each from $`s`:

* a terminator's exit hits UB after the acts $`t`; or returns, after $`t`,
  in $`s'`, giving its operands back with $`n` steps left; or goes to a
  block, after $`t`, from $`s'`, whose run with $`n` steps ends the path
  after $`t`;
* an op with no callee hits UB after $`t`, or gives results after $`t`,
  in $`s'`, from which the rest of the block runs with $`n` steps, after
  $`t`;
* a call's callee, in its frame, hits UB, or runs out of fuel, or returns
  values after $`t` in $`s'` with $`k` steps left, and the rest of the
  block runs from $`s'` with $`\min(k, n)` steps, after $`t`;
* a call to a symbol that names no function of the module, which declares
  it for the call's types: the external-call rule hits UB after $`t`, or
  gives results of the call's result types after $`t`, in $`s'`, from
  which the rest of the block runs with $`n` steps, after $`t`.
:::
