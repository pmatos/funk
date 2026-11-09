import VersoManual
import Fir.Core.Div
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on division rules, which renders
`Fir.Core.Div` (ADR-2026-11-05-2012). Each block explains declarations of
that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Division rules: readable blocks" =>

:::moduleDocs (fingerprint := "11492776682742033790")
:::

:::readable Fir.Core.divEv (pin := Fir.Ev) (pin := BitVec.intMin) (fingerprint := "7816947079132740565")
*Definition: how a division ends.* Take the name $`\mathit{op}` of a
division or remainder op, whether it is signed, and a function $`q` that
gives its result on two vectors of $`N` bits. On a dividend $`a` and a
divisor $`b`, values of $`\mathsf{i}N`, the op ends with a result or with
{ref "The-fir-specification--Execution--Poison-and-immediate-UB"}[immediate UB],
by the first case that applies, from the top:

1. When $`b` is poison: UB, with the reason "_op_ by poison".
2. When $`b` is 0: UB, "_op_ by zero".
3. When $`a` is poison, the op is signed and $`b` is $`-1`: UB, "_op_ of
   poison by -1".
4. When $`a` is poison: the result poison.
5. When the op is signed, $`a` is $`\mathrm{smin}_N` and $`b` is $`-1`:
   UB, "_op_ of the signed minimum by -1".
6. Otherwise: the result $`q(a, b)`.

Here $`-1` is the vector of $`N` ones, and $`\mathrm{smin}_N` the signed
minimum: a 1 followed by $`N - 1` zeros, which writes $`-2^{N-1}` in two's
complement. The text after "UB" is the reason the run gives, which is for
people: refinement ignores it.

These are the core ops whose failure hardware cannot defer: x86-64's
division instructions trap on a zero divisor and on the signed minimum
by $`-1`. A divisor of zero is UB, and so is a
poison divisor, which might be zero. A signed division of the signed
minimum by $`-1` is UB: its quotient, $`2^{N-1}`, does not fit. So is a
poison dividend by $`-1`, which might be the signed minimum; the rule that
gave poison there is not monotone, as
{ref "The-fir-specification--Execution--Semantics-the-obligations-reject"}[the rejected rule for sdiv]
shows, and UB lets a backend emit a bare x86-64 division, with no guard.
That holds for $`\mathsf{srem}` too, although its result would be 0:
x86-64's `idiv` traps on it. Otherwise a poison dividend gives
poison. A division ends in one of these two ways and never chooses, so
this definition is a function to its ending.
:::

:::readable Fir.Core.sdivWith Fir.Core.udivWith (pin := Fir.Core.divEv) (pin := BitVec.sdiv) (pin := BitVec.srem) (pin := BitVec.udiv) (pin := BitVec.umod) (fingerprint := "803816091463886245")
*Definition: the rules of $`\mathsf{sdiv}` and $`\mathsf{udiv}`.* For every
width $`N`, with or without the flag $`\mathsf{exact}`, each ends as the
cases of how a division ends say, $`\mathsf{sdiv}` as a signed op and $`\mathsf{udiv}` as
an unsigned one, with these results $`q(a, b)`:

$$`\begin{aligned} q_{\mathsf{sdiv}}(a, b) &= \mathrm{trunc}(\hat{a} / \hat{b}) \bmod 2^N \\ q_{\mathsf{udiv}}(a, b) &= \lfloor a / b \rfloor \end{aligned}`

With $`\mathsf{exact}`, the result is poison instead when the division
leaves a remainder: when $`\mathsf{srem}` or $`\mathsf{urem}`, below, would
not give 0.

Here $`\mathrm{trunc}(x)` rounds $`x` towards zero (it is not the op
$`\mathsf{trunc}`), $`\hat{a}` and
$`\hat{b}` are $`\mathrm{signed}_N(a)` and $`\mathrm{signed}_N(b)`, the
integers that $`a` and $`b` write in two's complement, and $`k \bmod 2^N` the
vector of $`N` bits that writes the remainder of $`k` divided by $`2^N`, as
in the {ref "The-fir-specification--Execution--Wrap-flag-rules"}[wrap flag rules].
$`\mathsf{exact}` is a promise that the division leaves no remainder, and a
broken promise gives poison, not UB (ADR-2026-10-29-2006). It is checked
only after the cases of UB, so a division that is UB with $`\mathsf{exact}`
is UB without it.
:::

:::readable Fir.Core.sremValues Fir.Core.uremValues (pin := Fir.Core.divEv) (pin := BitVec.srem) (pin := BitVec.umod) (fingerprint := "5856221874484006570")
*Definition: the rules of $`\mathsf{srem}` and $`\mathsf{urem}`.* For every
width $`N`, each ends as the cases of how a division ends say, $`\mathsf{srem}` as a
signed op and $`\mathsf{urem}` as an unsigned one, with these results:

$$`\begin{aligned} q_{\mathsf{srem}}(a, b) &= (\hat{a} - \hat{b} \cdot t) \bmod 2^N \\ q_{\mathsf{urem}}(a, b) &= a - b \cdot \lfloor a / b \rfloor \end{aligned}`

where $`\hat{a}` and $`\hat{b}` are the signed values of $`a` and $`b`, and
$`t = \mathrm{trunc}(\hat{a} / \hat{b})`, as for $`\mathsf{sdiv}`.
They are the remainders of $`\mathsf{sdiv}` and $`\mathsf{udiv}`, so the
remainder of $`\mathsf{srem}` has the sign of the dividend: $`-7` by 2
leaves $`-1`, and 7 by $`-2` leaves 1.
:::

:::readable Fir.Core.ruleOfEv (pin := Fir.Ev) (pin := Fir.MonadUB) (fingerprint := "4529996667052300154")
*Definition: a rule that may end with UB, for every way of computing.* Let
$`g` give, on two values $`a` and $`b` of $`\mathsf{i}N`, a result or
immediate UB with a reason. For every way of computing with the
{ref "The-fir-specification--Execution--Effects-and-op-semantics"}[UB effect],
the rule of $`g` takes the operands $`(a, b)`. When $`g(a, b)` ends with
the result $`v`, it gives $`v`; when $`g(a, b)` ends with UB with the reason
$`r`, it is $`\mathrm{ub}(r)`, which ends the run with immediate UB.

The divisions are written once as functions to their ending, which tests
can compare; this definition turns each into the rule that the
{ref "The-fir-specification--Execution--Core-op-semantics"}[core op semantics]
gives the op, for every way of computing with the UB effect: the spec's
set of the ways a run may end, and the tree of choices that `fir-ref` walks, alike.
:::
