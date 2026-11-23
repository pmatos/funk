import VersoManual
import Fir.Execution.Effects
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on effects and op semantics, which
renders `Fir.Execution.Effects` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Effects and op semantics: readable blocks" =>

:::moduleDocs (fingerprint := "12212311006221374468")
:::

:::readable Fir.MonadChoice (fingerprint := "17910636895159052972")
*Definition: the choice effect.* A computation may choose bits:
$`\mathrm{choose}(w)` gives $`w` arbitrary bits, a vector of $`w` bits that
nothing in the program fixes. A run that chooses can go on in
$`2^w` ways, one for each vector. $`\mathsf{freeze}` of poison chooses
once, and every use of the frozen value then sees the bits it chose
(ADR-2026-10-29-2017).

A float op whose result is a NaN chooses the NaN's sign and mantissa,
$`\mathrm{choose}_{\mathrm{nan}}(e, m)`, $`m + 1` bits of the format
$`\mathsf{float}\langle e,m\rangle`. It is $`\mathrm{choose}(m + 1)`
unless a monad says otherwise, and only the
{ref "The-fir-specification--Execution--Choice-trees"}[tree of choices]
does, to label the choice, so that a walk of the tree can try a few NaNs
where it cannot try them all (ADR-2026-11-16-0855).
:::

:::readable Fir.MonadUB (fingerprint := "13343653773008458106")
*Definition: the immediate UB effect.* A computation may end the run with
{ref "The-fir-specification--Execution--Poison-and-immediate-UB"}[immediate UB]:
$`\mathrm{ub}(\mathit{reason})` ends it at once, such as when a branch
condition is poison or a divisor is zero. The reason is text for people;
nothing in the semantics reads it. Unlike poison, UB is not a value: it is
an event, after which the run has no meaning.
:::

:::readable Fir.Exit (fingerprint := "3525567684497507043")
*Definition: where control goes when a block ends.* A terminator either
jumps to one of its successors or returns from the function.

```grammar Fir.Exit
\mathit{exit}
goto   \mathsf{goto}~i
ret    \mathsf{ret}
```

* $`\mathsf{goto}~i` goes to the terminator's successor with index $`i`,
  counting from 0.
* $`\mathsf{ret}` returns to the caller the terminator's operands.

The list may grow, for example for unwinding.
:::

:::readable Fir.DialectDenote (fingerprint := "12192561499539734519")
*Definition: the semantics of a dialect's ops.* Each dialect gives each of
its ops a meaning, in terms of the effects the dialect needs. Let the op
$`o` have operand types $`t_1, \dots, t_n` and result types
$`r_1, \dots, r_k`, as its
{ref "The-fir-specification--Abstract-syntax--Dialects"}[signature] says.

* $`\mathrm{denote}_o(v_1, \dots, v_n)`, for values
  $`v_i \in \llbracket t_i \rrbracket`, is a computation that ends with
  result values $`w_1, \dots, w_k`, with
  $`w_j \in \llbracket r_j \rrbracket`, or ends by an effect, such as
  immediate UB. The interpreter runs an op that is not a terminator by it.
* $`\mathrm{exit}_o(v_1, \dots, v_n)` is a computation that ends with an
  $`\mathit{exit}`: where control goes. The interpreter runs a terminator
  by it. On $`\mathsf{goto}~i`, the values passed to the target block are
  the ones the terminator lists for its successor $`i`, one for each
  argument of that block
  ({ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[successors]);
  on $`\mathsf{ret}`, the function returns the terminator's operands.
* $`\mathrm{pick}_o(\mathit{ok}, v_1, \dots, v_n)` is a computation that
  ends with a symbol $`s`, the function that $`o` calls, or ends by an
  effect, such as immediate UB. The interpreter runs it only for an op whose
  callee is picked when it runs (#235), and gives it the test
  $`\mathit{ok}`: $`\mathit{ok}(s)` holds when the module has a function,
  or an external declaration, with the symbol $`s`, that takes the values
  $`v_2, \dots, v_n` and gives the results $`r_1, \dots, r_k`.

The interpreter gives an op only values of its operand types. It checks
each operand's type before it runs the op, and the path is
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[stuck]
when one does not match, which validation rules out. The shape follows
LeanMLIR's (ADR-2026-10-29-2009).
:::

:::readable Fir.Callee (fingerprint := "16059132851290025235")
*Definition: the callee of an op.* An op that calls a function names its
callee, $`\mathsf{fixed}~s` for the symbol $`s`, as $`\mathsf{call}~@g`
names $`@g`; or its callee is $`\mathsf{picked}`: the op's rule picks the
symbol when the op runs, from its first operand, as a call through a
pointer does (#235), and the op passes its other operands to the callee.
:::

:::readable Fir.DialectCall (fingerprint := "8339298151678921278")
*Definition: the ops that call a function.* Each dialect says which of its
ops call a function of the module: for an op $`o`, $`\mathrm{callee}(o)`
is $`\mathsf{fixed}~s` when $`o` names the symbol $`s` of the function it
calls, $`\mathsf{picked}` when the rule $`\mathrm{pick}_o` picks the
symbol when $`o` runs, from its operands (#235, the human's ruling of
2026-11-19), or nothing when $`o` calls none. An op whose callee is picked
passes its operands but the first to the callee. In the core dialect,
$`\mathsf{call}~s` names $`s`, no other op calls a function, and no op
picks its callee.

The interpreter runs the callee with the fuel that the caller has left, as
the call effect above explains. It asks for the callee only of an op that is
not a terminator: a terminator runs by its exit, whatever
$`\mathrm{callee}` says of it.

Nothing ties $`\mathrm{callee}` to validation. The dialect's own
validation rule for a call must check that its callee is a function of the
module, and that the types of its operands and results match the callee's
signature, as the
{ref "The-fir-specification--Validation--Core-rules"}[core rule] for
$`\mathsf{call}` does.
:::
