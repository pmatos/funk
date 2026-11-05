import VersoManual
import Fir.Core.Ops
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on core ops, which renders `Fir.Core.Ops`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "Core ops: readable blocks" =>

:::readable Fir.Core.WrapFlags (fingerprint := "2440796118969772124")
*Wrap flags.* The ops `add`, `sub` and `mul` carry two flags. Each flag is a
promise about the operands, and when the promise is broken the result is
poison.

```grammar Fir.Core.WrapFlags
\mathit{flags}
nuw,nsw   \mathsf{nuw}^?~\mathsf{nsw}^?
```

* `nuw`, no unsigned wrap: read as unsigned integers, the operands give an
  exact result that fits in $`N` bits.
* `nsw`, no signed wrap: read as two's-complement signed integers, the
  operands give an exact result that fits in $`N` bits.

A flag is off unless the op sets it.
:::

:::readable Fir.Core.Pred (fingerprint := "11087752805963245739")
*Predicates.* A comparison asks one of ten questions about two integers.
`eq` and `ne` compare their bits. The `s` predicates read the integers as
signed, and the `u` predicates as unsigned: `lt` is less than, `le` less
or equal, `gt` greater than and `ge` greater or equal.

```grammar Fir.Core.Pred
\mathit{pred}
eq,ne             \mathsf{eq} \mid \mathsf{ne}
slt,sle,sgt,sge   \mathsf{slt} \mid \mathsf{sle} \mid \mathsf{sgt} \mid \mathsf{sge}
ult,ule,ugt,uge   \mathsf{ult} \mid \mathsf{ule} \mid \mathsf{ugt} \mid \mathsf{uge}
```
:::

:::readable Fir.Core.Op (fingerprint := "9094796732278286257")
*Ops.* An op of the core dialect carries the width $`N` of the integers it
works on, so the types of its operands and results follow from it. Below,
$`\mathsf{i}N` is the type of $`N`-bit integers, $`c` a constant of that
type, $`t` and $`r` types, and $`f` a function's symbol. The ops come in
eight families.

*Constants* put a fixed value in the program.

```grammar Fir.Core.Op
\mathit{op}
const   \mathsf{const}_N~c
```

* $`\mathsf{const}_N~c` is the constant $`c` of type $`\mathsf{i}N`. It has
  no operands, so it is never poison.

*Arithmetic* computes on integers of width $`N`. Results wrap modulo
$`2^N` unless a flag says otherwise.

```grammar Fir.Core.Op
\mathit{op}
-           \dots
add,sub,mul \mathsf{add}_N~\mathit{flags} \mid \mathsf{sub}_N~\mathit{flags} \mid \mathsf{mul}_N~\mathit{flags}
sdiv,udiv   \mathsf{sdiv}_N~\mathsf{exact}^? \mid \mathsf{udiv}_N~\mathsf{exact}^?
srem,urem   \mathsf{srem}_N \mid \mathsf{urem}_N
```

* `add`, `sub` and `mul` add, subtract and multiply. A broken flag gives
  poison.
* `sdiv` and `udiv` divide, reading the operands as signed or unsigned
  integers, and round towards zero. With `exact`, a non-zero remainder
  gives poison.
* `srem` and `urem` give the remainder of `sdiv` and `udiv`; for `srem` it
  has the sign of the dividend.
* A divisor of zero is immediate UB, and so is a poison divisor, which
  might be zero. `sdiv` and `srem` by $`-1` are immediate UB when the
  dividend is the signed minimum, or poison, which might be it. Otherwise
  a poison dividend gives poison.

*Bitwise ops and shifts* work on the bits of an integer.

```grammar Fir.Core.Op
\mathit{op}
-             \dots
and,or,xor    \mathsf{and}_N \mid \mathsf{or}_N \mid \mathsf{xor}_N
shl,lshr,ashr \mathsf{shl}_N \mid \mathsf{lshr}_N \mid \mathsf{ashr}_N
```

* `and`, `or` and `xor` combine their operands bit by bit.
* `shl` shifts left, `lshr` shifts right filling with zeros, and `ashr`
  shifts right filling with the sign bit. The second operand is the shift
  amount, read as unsigned. An amount of $`N` or more gives poison, and so
  does a poison amount.

*Comparison and selection* turn a question about integers into a bit, and
a bit into a choice.

```grammar Fir.Core.Op
\mathit{op}
-      \dots
icmp   \mathsf{icmp}_N~\mathit{pred}
select \mathsf{select}_N
```

* $`\mathsf{icmp}_N~\mathit{pred}` compares two $`\mathsf{i}N` values and
  gives an $`\mathsf{i1}`: 1 when the predicate holds, 0 when it does not.
* $`\mathsf{select}_N` takes an $`\mathsf{i1}` condition and two
  $`\mathsf{i}N` values, and gives one of them. The value not chosen does
  not matter, even when it is poison; the one chosen is given as it is.

  $$`\mathsf{select}_N(c, a, b) = \begin{cases} a & \text{if } c = 1 \\ b & \text{if } c = 0 \\ \mathsf{poison} & \text{if } c \text{ is poison} \end{cases}`

*Width changes* move an integer to another width.

```grammar Fir.Core.Op
\mathit{op}
-         \dots
zext,sext \mathsf{zext}_{M \to N} \mid \mathsf{sext}_{M \to N} \quad (M < N)
trunc     \mathsf{trunc}_{M \to N} \quad (N < M)
```

* `zext` fills the new high bits of an $`\mathsf{i}M` with zeros, and
  `sext` with its sign bit, giving an $`\mathsf{i}N`.
* `trunc` keeps the low $`N` bits of an $`\mathsf{i}M`.

*Poison control* writes poison and stops it.

```grammar Fir.Core.Op
\mathit{op}
-             \dots
freeze,poison \mathsf{freeze}_N \mid \mathsf{poison}_N
```

* `freeze` gives its operand unchanged when it is not poison. When it is
  poison, `freeze` gives an arbitrary but fixed value: every use of the
  result sees the same bits (ADR-2026-10-29-2006, ADR-2026-10-29-2017).
* $`\mathsf{poison}_N` is the poison of type $`\mathsf{i}N`, on every run.
  Native code may put any value of $`\mathsf{i}N` in its place, since every
  value refines poison.

*Control flow* ends a block: these ops are the terminators.

```grammar Fir.Core.Op
\mathit{op}
-         \dots
br,condBr \mathsf{br} \mid \mathsf{condbr}
ret       \mathsf{ret}~t^*
```

* `br` jumps to its one successor, passing it the successor's arguments. A
  poison argument arrives as poison.
* `condbr` takes an $`\mathsf{i1}` condition and has two successors. It
  jumps to the first when the condition is 1, and to the second when the
  condition is 0. Branching on poison is immediate UB.
* $`\mathsf{ret}~t^*` returns its operands, of the types $`t^*`, from the
  function: any number of them, each a value or poison
  (ADR-2026-10-30-0816).

*Calls* run another function of the module.

```grammar Fir.Core.Op
\mathit{op}
-    \dots
call \mathsf{call}~f : t^* \to r^*
```

* $`\mathsf{call}~f : t^* \to r^*` calls the function with symbol $`f`,
  passing operands of the types $`t^*` and receiving results of the types
  $`r^*`, any number of each. Poison passes through both ways: a poison
  operand is a poison argument, and a poison that the callee returns is a
  poison result. A function may call itself.
:::
