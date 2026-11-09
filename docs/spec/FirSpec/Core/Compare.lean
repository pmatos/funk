import VersoManual
import Fir.Core.Compare
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on comparison and selection rules, which
renders `Fir.Core.Compare` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Comparison and selection rules: readable blocks" =>

:::moduleDocs (fingerprint := "16989213570490224332")
:::

:::readable Fir.Core.Pred.holds (pin := Fir.Core.Pred) (pin := BitVec.slt) (pin := BitVec.sle) (pin := BitVec.ult) (pin := BitVec.ule) (fingerprint := "18133733643993984354")
*Definition: when a predicate holds.* For every width $`N`, each of the ten
{ref "The-fir-specification--Abstract-syntax--Core-ops"}[predicates] holds
of two vectors $`a, b \in \mathbb{B}^N`, the set of vectors of $`N` bits,
or not, as follows:

$$`\begin{array}{ll} \mathsf{eq}: a = b & \mathsf{ne}: a \neq b \\ \mathsf{slt}: \mathrm{s}(a) < \mathrm{s}(b) & \mathsf{ult}: a < b \\ \mathsf{sle}: \mathrm{s}(a) \leq \mathrm{s}(b) & \mathsf{ule}: a \leq b \\ \mathsf{sgt}: \mathrm{s}(a) > \mathrm{s}(b) & \mathsf{ugt}: a > b \\ \mathsf{sge}: \mathrm{s}(a) \geq \mathrm{s}(b) & \mathsf{uge}: a \geq b \end{array}`

Here $`\mathrm{s}(a)` is $`\mathrm{signed}_N(a)`, the integer that $`a`
writes in two's complement, as in the
{ref "The-fir-specification--Execution--Wrap-flag-rules"}[wrap flag rules],
and on the right a vector stands for the number it writes in binary, read
as unsigned. $`\mathsf{eq}` and $`\mathsf{ne}` compare the bits. One pair
of vectors can be in one order read as signed and in the other read as
unsigned: at $`\mathsf{i8}`, all ones is $`-1` read as signed, less than 1,
and 255 read as unsigned, greater.
:::

:::readable Fir.Core.icmpValues (fingerprint := "6864812519093970360")
*Definition: the rule of $`\mathsf{icmp}`.* For every width $`N` and
predicate $`p`, $`\mathsf{icmp}_N~p` of two vectors of bits is the
$`\mathsf{i1}` value 1 when $`p` holds of them and 0 when it does not; a
poison operand, in either place, gives poison:

$$`\mathsf{icmp}_N~p\,(a, b) = \begin{cases} 1 & \text{if } p \text{ holds of } a, b \\ 0 & \text{if it does not} \end{cases}`

for $`a` and $`b` in $`\mathbb{B}^N`, and $`\mathsf{icmp}_N~p\,(a, b)` is
poison when $`a` or $`b` is poison.

$`\mathsf{icmp}` is never UB, and it
{ref "The-fir-specification--Execution--Poison-classes"}[propagates poison]
(ADR-2026-10-30-0818). So $`\mathsf{icmp}~\mathsf{eq}` of a poison with
itself is poison, not 1.
:::

:::readable Fir.Core.selectValues (fingerprint := "4457794252016800458")
*Definition: the rule of $`\mathsf{select}`.* For every width $`N`,
$`\mathsf{select}_N` takes an $`\mathsf{i1}` condition $`c` and two values
$`a` and $`b` of $`\mathsf{i}N`. It gives $`a`, as it is, when $`c` is 1,
and $`b`, as it is, when $`c` is 0; a poison condition gives poison:

$$`\mathsf{select}_N(c, a, b) = \begin{cases} a & \text{if } c = 1 \\ b & \text{if } c = 0 \\ \mathsf{poison} & \text{if } c \text{ is poison} \end{cases}`

The value not chosen does not matter, even when it is poison, and the value
chosen is given as it is, poison or not. So $`\mathsf{select}` is an
exception to
{ref "The-fir-specification--Execution--Poison-classes"}[poison propagation]
(ADR-2026-10-30-0818): it gives poison only through its condition or the
value it chooses. That is why $`\mathsf{select}_1(c, x, 0)` is not
$`\mathsf{and}_1(c, x)`: when $`c` is 0, the first gives 0 whatever $`x` is,
and the second gives poison when $`x` is poison. It is never UB.
:::

:::readable Fir.Core.predResults (pin := Fir.Core.Pred.all) (fingerprint := "17618576176253495559")
*Definition: what the ten predicates give on two ordered values, for the
tests.* For an order $`s` of two values read as signed and an order $`u`
of them read as unsigned, each one of less, equal and greater, the list of
whether each predicate holds, in the order $`\mathsf{eq}`, $`\mathsf{ne}`,
$`\mathsf{slt}`, $`\mathsf{sle}`, $`\mathsf{sgt}`, $`\mathsf{sge}`,
$`\mathsf{ult}`, $`\mathsf{ule}`, $`\mathsf{ugt}` and $`\mathsf{uge}`.
$`\mathsf{eq}` and $`\mathsf{ne}` read the signed order.
:::

:::readable Fir.Core.comparesAs (pin := Fir.Core.Pred.all) (pin := Fir.Core.icmpValues) (pin := Fir.Core.predResults) (fingerprint := "10986874702210396338")
*Definition: a test that two values compare in given orders.* For two
vectors $`a` and $`b` of $`N` bits and orders $`s` and $`u`, the test holds
when $`\mathsf{icmp}_N~p\,(a, b)`, for each predicate $`p` in the order
above, gives the value that the list of the previous block says, 1 for
holds and 0 for does not.
:::

:::readable Fir.Core.boundaryPairs (pin := BitVec.intMin) (pin := BitVec.intMax) (fingerprint := "7326674571296004669")
*Definition: pairs of boundary values, for the tests.* For a width $`N`, a
list of fourteen pairs of vectors of $`N` bits, each with its order read as
signed and its order read as unsigned. They are built from 0, 1, all ones,
the signed minimum, a 1 followed by $`N - 1` zeros, and the signed maximum,
a 0 followed by $`N - 1` ones, and include pairs whose signed order is not
their unsigned order. The orders are right only when $`N \geq 3`, where
these five values are distinct; the tests use them at $`\mathsf{i7}`,
$`\mathsf{i8}`, $`\mathsf{i33}`, $`\mathsf{i64}` and $`\mathsf{i128}`.
:::
