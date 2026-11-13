import VersoManual
import Fir.Core.FloatCompare
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the float comparison rules, which
renders `Fir.Core.FloatCompare` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Float comparison rules: readable blocks" =>

:::moduleDocs (fingerprint := "9065455117763472156")
:::

:::readable Fir.Core.floatCompare (fingerprint := "16383978172134608434")
*Definition: how two floats compare.* For every format
$`\mathsf{float}\langle e,m \rangle` with $`e \ge 2` and $`m \ge 1`, and
two vectors $`a, b \in \mathbb{B}^{1+e+m}`,
$`\mathrm{fcompare}_{e,m}(a, b)` is how the values that $`a` and $`b`
encode compare: $`<`, $`=` or $`>`, or $`\bot` when they are unordered.
Both come from Lean's float model: $`\mathrm{unpack}` reads a vector as a
signed zero, a finite number, a signed infinity or a NaN, and
$`\mathrm{compare}` orders two of them as IEEE 754 does. So

$$`\mathrm{fcompare}_{e,m}(a, b) = \begin{cases} \bot & \text{if } a \text{ or } b \text{ is a NaN} \\ \mathrm{order}(x_a, x_b) & \text{otherwise} \end{cases}`

where $`x_a` and $`x_b` are the numbers $`a` and $`b` encode, with
$`-\infty` and $`+\infty` at the ends and $`-0 = +0`. A NaN's payload and
sign play no part. Every pair of a format the model does not have, which
validation rejects, is unordered, so that the rule is total.
:::

:::readable Fir.Core.FPred.holds (pin := Fir.Core.FPred) (fingerprint := "18208178558884204792")
*Definition: when a float predicate holds.* Each of the fourteen
{ref "The-fir-specification--Abstract-syntax--Core-ops"}[float predicates]
holds of a pair that compares as $`c`, or not, as follows, where $`\bot`
is unordered:

$$`\begin{array}{ll} \mathsf{oeq}: c = (=) & \mathsf{ueq}: c \in \{\bot, =\} \\ \mathsf{one}: c \in \{<, >\} & \mathsf{une}: c \neq (=) \\ \mathsf{olt}: c = (<) & \mathsf{ult}: c \in \{\bot, <\} \\ \mathsf{ole}: c \in \{<, =\} & \mathsf{ule}: c \neq (>) \\ \mathsf{ogt}: c = (>) & \mathsf{ugt}: c \in \{\bot, >\} \\ \mathsf{oge}: c \in \{>, =\} & \mathsf{uge}: c \neq (<) \\ \mathsf{ord}: c \neq \bot & \mathsf{uno}: c = \bot \end{array}`

Each $`\mathsf{u}` predicate is the negation of an $`\mathsf{o}` one:
$`\mathsf{une}` of $`\mathsf{oeq}`, $`\mathsf{ueq}` of $`\mathsf{one}`,
$`\mathsf{uge}` of $`\mathsf{olt}`, and so on, and $`\mathsf{uno}` of
$`\mathsf{ord}`.
:::

:::readable Fir.Core.fcmpValues (fingerprint := "10639262800556838397")
*Definition: the rule of $`\mathsf{fcmp}`.* For every format
$`\mathsf{float}\langle e,m \rangle`, float predicate $`p` and flags
$`\phi`, $`\mathsf{fcmp}_{e,m}~\phi~p` of two values gives an
$`\mathsf{i1}`:

$$`\mathsf{fcmp}_{e,m}~\phi~p\,(a, b) = \begin{cases} \mathsf{poison} & \text{if } a \text{ or } b \text{ is poison, or } [a, b] \text{ breaks } \phi \\ 1 & \text{else if } p \text{ holds of } \mathrm{fcompare}_{e,m}(a, b) \\ 0 & \text{otherwise} \end{cases}`

The operands break $`\phi` as the
{ref "The-fir-specification--Execution--Fast-math-flag-rules"}[fast-math flag rules]
say: a NaN under $`\mathsf{nnan}`, or an infinity under
$`\mathsf{ninf}`. $`\mathsf{nsz}` changes nothing, since the result is not
a float.

It is never UB and never gives a NaN: its result is a bit. So
$`\mathsf{fcmp}~\mathsf{oeq}` of a NaN with itself gives 0, and
$`\mathsf{fcmp}~\mathsf{une}` gives 1.
:::

:::readable Fir.Core.cmp32 Fir.Core.fpredResults Fir.Core.fcmpsAs (fingerprint := "6261801356151191241")
*Tests.* $`\mathrm{cmp32}` is $`\mathrm{fcompare}_{8,23}`, the order of
$`\mathsf{f32}`. $`\mathrm{fpredResults}(c)` lists what the fourteen
predicates give, in the order of the grammar, on a pair that compares as
$`c`, and $`\mathrm{fcmpsAs}` checks that $`\mathsf{fcmp}` gives exactly
that on two vectors. On every build, checks run them on zeros of both
signs, subnormals, ones, the largest finite values, infinities, and NaNs
quiet and signalling, with payloads and either sign, at $`\mathsf{f32}`,
$`\mathsf{f64}`, $`\mathsf{f16}`, $`\mathsf{bf16}`, $`\mathsf{f128}` and
$`\mathsf{float}\langle 2,1 \rangle`, and on poison operands.
:::
