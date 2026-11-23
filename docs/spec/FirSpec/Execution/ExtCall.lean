import VersoManual
import Fir.Execution.ExtCall
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the external-call rule, which renders
`Fir.Execution.ExtCall` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The external-call rule: readable blocks" =>

:::moduleDocs (fingerprint := "981855685700279059")
:::

:::readable Fir.DialectExtCall (fingerprint := "8593152062043629551")
*Definition: the external-call rule.* A dialect's external-call rule in a
way of computing $`m` gives, for the symbol $`g` of an external
declaration, the arguments $`w_1, \dots, w_n` of a call, each a typed
value, and the call's result types $`r_1, \dots, r_k`, a computation in
$`m`, $`\mathrm{ext}(g, [w_1, \dots, w_n], [r_1, \dots, r_k])`, of the
call's results, each a typed value. The interpreter checks that the
results have the types $`r_1, \dots, r_k`.
:::

:::readable Fir.DialectRun (pin := Fir.DialectDenote) (fingerprint := "2084966955205077144")
*Definition: a dialect's semantics with its external-call rule.* The
semantics of a dialect's ops in $`m` together with its external-call rule
in $`m`. It is what the traced layer takes of a dialect, since there the
dialect gives the rule, and the world answers the call.
:::

:::readable Fir.extCallUB Fir.extCall_setM (pin := Fir.instDialectExtCallSetM) (pin := Fir.MonadUB) (fingerprint := "7435596424721000302")
*Definition: the stand-in of the layers with no world.* In the set monad,
an external call is UB, with the reason "an external call has no meaning
without a world":
$$`\mathrm{ext}(g, \mathit{args}, \mathit{rs}) = \mathrm{ub}.`

*Theorem.* So the set monad's runs of a call to a declaration end in UB,
whatever the symbol, the arguments and the result types.
:::

:::readable Fir.Extern.accepts (pin := Fir.Extern) (fingerprint := "5190181777891803921")
*Definition: a declaration accepts a call.* An external declaration with
the parameter types $`p_1, \dots, p_m` and the result types
$`r'_1, \dots, r'_l` accepts a call on operands of the types
$`t_1, \dots, t_n` for results of the types $`r_1, \dots, r_k` when
$`[r'_1, \dots, r'_l] = [r_1, \dots, r_k]` and

* $`[p_1, \dots, p_m] = [t_1, \dots, t_n]`, when the declaration is not
  variadic;
* $`[t_1, \dots, t_n]` starts with $`[p_1, \dots, p_m]`, so $`m \le n`
  and $`t_i = p_i` for each $`i \le m`, when it is variadic, ends in
  `...`: the operands after the first $`m` are its variadic arguments.
:::

:::readable Fir.Module.declares (pin := Fir.Extern.accepts) (fingerprint := "1406666686694708645")
*Definition: a module declares a symbol for a call.* A module $`M`
declares the symbol $`g` for operands of the types $`t_1, \dots, t_n` and
results of the types $`r_1, \dots, r_k` when one of its items is an
external declaration named $`g` that accepts a call on those types. The
interpreter hands a call of $`g` that names no function of $`M` to the
external-call rule only then; otherwise the call is stuck.
:::
