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

:::readable Fir.MonadChoice (fingerprint := "4733032598783633289")
*Definition: the choice effect.* A computation may choose bits:
$`\mathrm{choose}(w)` gives $`w` arbitrary bits, a vector of $`w` bits that
nothing in the program fixes. A run that chooses can go on in
$`2^w` ways, one for each vector. $`\mathsf{freeze}` of poison chooses
once, and every use of the frozen value then sees the bits it chose
(ADR-2026-10-29-2017).
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

:::readable Fir.DialectDenote (fingerprint := "3730882492881147332")
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
  by it. The values passed to a successor are its successor arguments, and
  a return returns the terminator's operands.

The interpreter gives an op only values of its operand types. It checks
each operand's type before it runs the op, and the path is
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[stuck]
when one does not match, which validation rules out. The shape follows
LeanMLIR's (ADR-2026-10-29-2030).
:::

:::readable Fir.DialectCall (fingerprint := "3266187945828972356")
*Definition: the ops that call a function.* Each dialect says which of its
ops call a function of the module: for an op $`o`, $`\mathrm{callee}(o)`
is the symbol $`s` of the function that $`o` calls, or nothing when $`o`
calls none. In the core dialect, $`\mathsf{call}~s` calls $`s`, and no
other op calls a function.

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
