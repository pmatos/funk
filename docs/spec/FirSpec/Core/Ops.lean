import VersoManual
import Fir.Core.Ops
import Fir.Core.Validation
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on core ops, which renders `Fir.Core.Ops`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "Core ops: readable blocks" =>

:::moduleDocs (fingerprint := "7909701173623930783")
:::

:::readable Fir.Core.WrapFlags (fingerprint := "2440796118969772124")
*Wrap flags.* The ops $`\mathsf{add}`, $`\mathsf{sub}` and $`\mathsf{mul}`
carry two flags. Each flag is a promise about the operands, and when the
promise is broken the result is
{ref "The-fir-specification--Execution--Poison-and-immediate-UB"}[poison].

```grammar Fir.Core.WrapFlags
\mathit{flags}
nuw,nsw   \mathsf{nuw}^?~\mathsf{nsw}^?
```

* $`\mathsf{nuw}`, no unsigned wrap: read as unsigned integers, the
  operands give an exact result that fits in $`N` bits.
* $`\mathsf{nsw}`, no signed wrap: read as two's-complement signed
  integers, the operands give an exact result that fits in $`N` bits.

A flag is off unless the op sets it.
:::

:::readable Fir.Core.Pred (fingerprint := "11087752805963245739")
*Predicates.* A comparison asks one of ten questions about two integers.
$`\mathsf{eq}` and $`\mathsf{ne}` compare their bits. The $`\mathsf{s}`
predicates read the integers as signed, and the $`\mathsf{u}` predicates as
unsigned: $`\mathsf{lt}` is less than, $`\mathsf{le}` less or equal,
$`\mathsf{gt}` greater than and $`\mathsf{ge}` greater or equal.

```grammar Fir.Core.Pred
\mathit{pred}
eq,ne             \mathsf{eq} \mid \mathsf{ne}
slt,sle,sgt,sge   \mathsf{slt} \mid \mathsf{sle} \mid \mathsf{sgt} \mid \mathsf{sge}
ult,ule,ugt,uge   \mathsf{ult} \mid \mathsf{ule} \mid \mathsf{ugt} \mid \mathsf{uge}
```
:::

:::readable Fir.Core.FPred (fingerprint := "7187194159295087930")
*Float predicates.* A float comparison asks one of fourteen questions about
two floats (ADR-2026-11-09-1549). It compares the numbers they encode, so
$`-0` equals $`+0`. A NaN encodes no number, and a pair with a NaN is
_unordered_. The $`\mathsf{o}` predicates are _ordered_: each is false on
an unordered pair. The $`\mathsf{u}` predicates are _unordered_: each is
true on one. Otherwise $`\mathsf{eq}` is equal, $`\mathsf{ne}` not equal,
$`\mathsf{lt}` less than, $`\mathsf{le}` less or equal, $`\mathsf{gt}`
greater than and $`\mathsf{ge}` greater or equal. $`\mathsf{ord}` holds of
an ordered pair, and $`\mathsf{uno}` of an unordered one.

```grammar Fir.Core.FPred
\mathit{fpred}
oeq,one,olt,ole   \mathsf{oeq} \mid \mathsf{one} \mid \mathsf{olt} \mid \mathsf{ole}
ogt,oge,ord       \mathsf{ogt} \mid \mathsf{oge} \mid \mathsf{ord}
ueq,une,ult,ule   \mathsf{ueq} \mid \mathsf{une} \mid \mathsf{ult} \mid \mathsf{ule}
ugt,uge,uno       \mathsf{ugt} \mid \mathsf{uge} \mid \mathsf{uno}
```
:::

:::readable Fir.Core.FastMath Fir.Core.FastMath.Reserved (fingerprint := "1415803108012639584")
*Fast-math flags.* A float op carries the fast-math flags
(ADR-2026-11-09-1549). Each of the first three is a promise about the
op's operands or result:

```grammar Fir.Core.FastMath
\mathit{fmf}
nnan,ninf,nsz      \mathsf{nnan}^?~\mathsf{ninf}^?~\mathsf{nsz}^?
contract,reassoc   \mathsf{contract}^?~\mathsf{reassoc}^?
```

* $`\mathsf{nnan}`, no NaNs: no operand and no result is a NaN. A NaN
  operand or result gives
  {ref "The-fir-specification--Execution--Poison-and-immediate-UB"}[poison].
* $`\mathsf{ninf}`, no infinities: no operand and no result is an
  infinity. An infinite operand or result gives poison.
* $`\mathsf{nsz}`, no signed zeros: the sign of a zero result does not
  matter, so a zero result is $`+0` or $`-0`, a choice.

$`\mathsf{contract}` and $`\mathsf{reassoc}` are _reserved_: they are
permissions for passes, which M2's optimizer decides, not meanings of an
op. Validation rejects an op that carries either, and the rules ignore
them. A flag is off unless the op sets it.
:::

:::readable Fir.Core.FBin Fir.Core.FUnary (fingerprint := "4350115894855268594")
*Float operations.* The float arithmetic has six ops of two operands and
three of one (ADR-2026-11-09-1549). Each that rounds rounds to nearest,
ties to even.

```grammar Fir.Core.FBin
\mathit{fbin}
fadd,fsub,fmul,fdiv   \mathsf{fadd} \mid \mathsf{fsub} \mid \mathsf{fmul} \mid \mathsf{fdiv}
frem,fmod             \mathsf{frem} \mid \mathsf{fmod}
```

```grammar Fir.Core.FUnary
\mathit{funary}
fneg,fabs,sqrt   \mathsf{fneg} \mid \mathsf{fabs} \mid \mathsf{sqrt}
```

* $`\mathsf{fadd}` adds, $`\mathsf{fsub}` subtracts the second operand
  from the first, $`\mathsf{fmul}` multiplies and $`\mathsf{fdiv}` divides
  the first by the second.
* $`\mathsf{frem}` and $`\mathsf{fmod}` give the remainder of the first
  by the second, $`x - n \times y`, which is exact, so neither rounds. For
  $`\mathsf{frem}`, IEEE 754's remainder, $`n` is the quotient rounded to
  nearest, ties to even; for $`\mathsf{fmod}`, C's `fmod`, it is the
  quotient truncated. LLVM's `frem` is $`\mathsf{fmod}`, not
  $`\mathsf{frem}` (#310).
* $`\mathsf{fneg}` negates and $`\mathsf{fabs}` gives the absolute value;
  neither rounds. $`\mathsf{sqrt}` gives the square root, rounded.
:::

:::readable Fir.Core.Op (pin := Fir.Core.Op.Valid) (fingerprint := "18128408174805461646")
*Ops.* An op of the core dialect carries the width $`N` of the integers it
works on, or the format $`\mathsf{float}\langle e,m \rangle` of the floats
it works on, so the types of its operands and results follow from it.
Below, $`c` is a constant of type $`\mathsf{i}N`, $`v` a vector of
$`1+e+m` bits, $`t` and $`r` are types, and $`f` is a function's symbol. The ops come in fifteen families.

*Constants* put a fixed value in the program.

```grammar Fir.Core.Op
\mathit{op}
const   \mathsf{const}_N~c
fconst  \mathsf{const}_{e,m}~v
```

* $`\mathsf{const}_N~c` is the constant $`c` of type $`\mathsf{i}N`. It has
  no operands, so it is never poison.
* $`\mathsf{const}_{e,m}~v` (`fconst` in the Lean) is the float of
  $`\mathsf{float}\langle e,m \rangle` whose bits are $`v`: a sign bit,
  $`e` exponent bits and $`m` mantissa bits. Every bit pattern is a
  constant, a NaN's payload and sign included, and has one spelling in text
  (ADR-2026-11-11-1438). It is
  never poison either.

*Arithmetic* computes on integers of width $`N`. Results wrap modulo
$`2^N` unless a flag says otherwise.

```grammar Fir.Core.Op
\mathit{op}
-           \dots
add,sub,mul \mathsf{add}_N~\mathit{flags} \mid \mathsf{sub}_N~\mathit{flags} \mid \mathsf{mul}_N~\mathit{flags}
sdiv,udiv   \mathsf{sdiv}_N~\mathsf{exact}^? \mid \mathsf{udiv}_N~\mathsf{exact}^?
srem,urem   \mathsf{srem}_N \mid \mathsf{urem}_N
```

* $`\mathsf{add}`, $`\mathsf{sub}` and $`\mathsf{mul}` add, subtract and
  multiply. A broken flag gives poison.
* $`\mathsf{sdiv}` and $`\mathsf{udiv}` divide, reading the operands as
  signed or unsigned integers, and round towards zero. With
  $`\mathsf{exact}`, a non-zero remainder gives poison.
* $`\mathsf{srem}` and $`\mathsf{urem}` give the remainder of
  $`\mathsf{sdiv}` and $`\mathsf{udiv}`; for $`\mathsf{srem}` it has the
  sign of the dividend.
* A divisor of zero is
  {ref "The-fir-specification--Execution--Poison-and-immediate-UB"}[immediate UB],
  and so is a poison divisor, which might be zero. $`\mathsf{sdiv}` and
  $`\mathsf{srem}` by $`-1` are immediate UB when the dividend is the
  signed minimum, or poison, which might be it. Otherwise a poison dividend
  gives poison.

*Bitwise ops and shifts* work on the bits of an integer.

```grammar Fir.Core.Op
\mathit{op}
-             \dots
and,or,xor    \mathsf{and}_N \mid \mathsf{or}_N \mid \mathsf{xor}_N
shl,lshr,ashr \mathsf{shl}_N \mid \mathsf{lshr}_N \mid \mathsf{ashr}_N
```

* $`\mathsf{and}`, $`\mathsf{or}` and $`\mathsf{xor}` combine their
  operands bit by bit.
* $`\mathsf{shl}` shifts left, $`\mathsf{lshr}` shifts right filling with
  zeros, and $`\mathsf{ashr}` shifts right filling with the sign bit. The
  second operand is the shift amount, read as unsigned. An amount of $`N`
  or more gives poison, and so does a poison amount.

*Comparison and selection* turn a question about integers or floats into
a bit, and a bit into a choice.

```grammar Fir.Core.Op
\mathit{op}
-      \dots
icmp   \mathsf{icmp}_N~\mathit{pred}
fcmp   \mathsf{fcmp}_{e,m}~\mathit{fmf}~\mathit{fpred}
select \mathsf{select}_N
```

* $`\mathsf{icmp}_N~\mathit{pred}` compares two $`\mathsf{i}N` values and
  gives an $`\mathsf{i1}`: 1 when the predicate holds, 0 when it does not.
* $`\mathsf{fcmp}_{e,m}~\mathit{fmf}~\mathit{fpred}` compares two values of
  $`\mathsf{float}\langle e,m \rangle` by the numbers they encode in Lean's
  float model, and gives an $`\mathsf{i1}` in the same way. It is never
  UB, and a poison operand gives poison, as does an operand that breaks
  $`\mathsf{nnan}` or $`\mathsf{ninf}`.
* $`\mathsf{select}_N` takes an $`\mathsf{i1}` condition and two
  $`\mathsf{i}N` values, and gives one of them. The value not chosen does
  not matter, even when it is poison; the one chosen is given as it is.

  $$`\mathsf{select}_N(c, a, b) = \begin{cases} a & \text{if } c = 1 \\ b & \text{if } c = 0 \\ \mathsf{poison} & \text{if } c \text{ is poison} \end{cases}`

*Float arithmetic* computes on floats of one format
$`\mathsf{float}\langle e,m \rangle`, by Lean's float model
(ADR-2026-11-09-1549).

```grammar Fir.Core.Op
\mathit{op}
-       \dots
fbin    \mathit{fbin}_{e,m}~\mathit{fmf}
funary  \mathit{funary}_{e,m}~\mathit{fmf}
fma     \mathsf{fma}_{e,m}~\mathit{fmf}
```

* $`\mathit{fbin}_{e,m}` (`fbin` in the Lean) takes two values and
  $`\mathit{funary}_{e,m}` (`funary`) one, and each gives the model's
  result, rounded to nearest even where the op rounds.
* $`\mathsf{fma}_{e,m}` gives $`a \times b + c` of three values, rounded
  once.
* When the model's result is a NaN, the op gives any NaN of the format:
  its sign and payload are a choice. None is ever UB, and a poison operand
  gives poison.
* Each carries its fast-math flags $`\mathit{fmf}`: an operand or result
  that breaks $`\mathsf{nnan}` or $`\mathsf{ninf}` gives poison, and with
  $`\mathsf{nsz}` a zero result has either sign.

*Width changes* move an integer to another width.

```grammar Fir.Core.Op
\mathit{op}
-         \dots
zext,sext \mathsf{zext}_{M \to N} \mid \mathsf{sext}_{M \to N}
trunc     \mathsf{trunc}_{M \to N}
```

* $`\mathsf{zext}` fills the new high bits of an $`\mathsf{i}M` with
  zeros, and $`\mathsf{sext}` with its sign bit, giving an $`\mathsf{i}N`.
* $`\mathsf{trunc}` keeps the low $`N` bits of an $`\mathsf{i}M`.

*Bit casts* read the same bits as another type (ADR-2026-11-09-1549).

```grammar Fir.Core.Op
\mathit{op}
-             \dots
toBits,ofBits \mathsf{bitcast}_{e,m}^{\to \mathsf{i}} \mid \mathsf{bitcast}_{e,m}^{\mathsf{i} \to}
```

* $`\mathsf{bitcast}_{e,m}^{\to \mathsf{i}}` (`toBits` in the Lean)
  gives the bits of a value of $`\mathsf{float}\langle e,m \rangle` as an
  $`\mathsf{i}N` with $`N = 1+e+m`, and
  $`\mathsf{bitcast}_{e,m}^{\mathsf{i} \to}` (`ofBits`) gives the float
  whose bits are those of an $`\mathsf{i}N`. No bit changes, a NaN's sign
  and payload included. Neither is ever UB, and a poison operand gives
  poison.

*Conversions from integers* give the float nearest an integer
(ADR-2026-11-09-1549).

```grammar Fir.Core.Op
\mathit{op}
-             \dots
sitofp,uitofp \mathsf{sitofp}_{N,e,m} \mid \mathsf{uitofp}_{N,e,m}
```

* $`\mathsf{sitofp}_{N,e,m}` reads an $`\mathsf{i}N` as a signed integer,
  and $`\mathsf{uitofp}_{N,e,m}` as an unsigned one, and each gives that
  integer as a value of $`\mathsf{float}\langle e,m \rangle`, rounded to
  nearest, ties to even, in Lean's float model. An integer too large for
  the format gives an infinity of its sign, and $`0` gives $`+0`. Neither
  is ever UB or gives a NaN, and a poison operand gives poison.

*Conversions between formats* give a float's number in another format
(ADR-2026-11-09-1549).

```grammar Fir.Core.Op
\mathit{op}
-             \dots
fpext,fptrunc \mathsf{fpext}_{e,m,e',m'} \mid \mathsf{fptrunc}_{e,m,e',m'}
```

* $`\mathsf{fpext}_{e,m,e',m'}` gives a value of
  $`\mathsf{float}\langle e,m \rangle` as a value of
  $`\mathsf{float}\langle e',m' \rangle`, a format that holds every value
  of it, with $`e \le e'` and $`m \le m'`, so it never rounds; and
  $`\mathsf{fptrunc}_{e,m,e',m'}` rounds it, to nearest, ties to even,
  into a format that cannot hold every value of it, with $`e' < e` or
  $`m' < m`. The
  {ref "The-fir-specification--Validation--Core-rules"}[core rules] give
  every ordered pair of two formats to exactly one of the two (the human's
  ruling of 2026-11-12 on #354). A number too large for the target gives
  an infinity of its sign, one too small a zero of its sign, and a NaN any
  NaN of the target. Neither is ever UB, and a poison operand gives
  poison.

*Pointer offsets* move a pointer within its memory (#231).

```grammar Fir.Core.Op
\mathit{op}
-      \dots
ptradd \mathsf{ptradd}_{N,W}
```

* $`\mathsf{ptradd}_{N,W}` moves a pointer of
  $`\mathsf{ptr}\langle N \rangle` by the integer that an
  $`\mathsf{i}W` holds, read as signed, in units of the memory $`N`. The
  result keeps the pointer's provenance. Its offset may leave the bounds
  of the allocation: only an access through it must be in bounds
  (ADR-2026-11-13-0251). It is never UB, and a poison operand gives
  poison.

*Stack allocation* makes room in a memory for the current call (#231; the
human's ruling of 2026-11-14 on #378).

```grammar Fir.Core.Op
\mathit{op}
-      \dots
alloca \mathsf{alloca}_{N}~k~t~c~a
```

* $`\mathsf{alloca}_{N}~k~t~c~a` allocates room for $`c` values of the
  type $`t` in the memory $`N`, with the kind $`k`, and gives a pointer of
  $`\mathsf{ptr}\langle N \rangle` to the first unit of the allocation.
  It takes $`c` times the units of $`t` in that memory, aligned to $`a`
  units, or to the natural alignment of $`t` when $`a` is none. Its units
  are poison until a store writes them, and a stack allocation is freed
  when the call that made it returns. It has no operands, is never UB, and
  never gives poison; it allocates in the memory $`N`. The
  {ref "The-fir-specification--Validation--Core-rules"}[core rules]
  accept only the kind $`\mathsf{stack}`, a count of at least 1, an
  alignment that is a power of two, and an integer type
  (ADR-2026-11-14-0915).

*Conversions to integers* give a float's number truncated toward zero as
an integer (ADR-2026-11-09-1549; the human's ruling of 2026-11-12 on #354).

```grammar Fir.Core.Op
\mathit{op}
-             \dots
fptosi,fptoui \mathsf{fptosi}_{e,m,N} \mid \mathsf{fptoui}_{e,m,N}
```

* $`\mathsf{fptosi}_{e,m,N}` cuts the fraction of a value of
  $`\mathsf{float}\langle e,m \rangle` off, toward zero, so $`2.7` gives
  $`2` and $`-2.7` gives $`-2`, and gives the integer as a signed value of
  $`\mathsf{i}N`; $`\mathsf{fptoui}_{e,m,N}` gives it as an unsigned one.
  An integer that $`\mathsf{i}N` does not hold, an infinity and a NaN give
  poison. Neither rounds, so neither has a rounding attribute, and neither
  is ever UB. A poison operand gives poison.

*Poison control* writes poison and stops it.

```grammar Fir.Core.Op
\mathit{op}
-             \dots
freeze,poison \mathsf{freeze}_N \mid \mathsf{poison}_N
```

* $`\mathsf{freeze}` gives its operand unchanged when it is not poison.
  When it is poison, $`\mathsf{freeze}` gives an arbitrary but fixed
  value: every use of the result sees the same bits (ADR-2026-10-29-2006,
  ADR-2026-10-29-2017).
* $`\mathsf{poison}_N` is the poison of type $`\mathsf{i}N`, on every run.
  Native code may put any value of $`\mathsf{i}N` in its place, since every
  value refines poison.

*Control flow* ends a block: these ops are the terminators.

```grammar Fir.Core.Op
\mathit{op}
-         \dots
br,condBr   \mathsf{br} \mid \mathsf{cond\_br}
ret         \mathsf{ret}~t^*
unreachable \mathsf{unreachable}
```

* $`\mathsf{br}` jumps to its one successor, passing it the successor's
  arguments. A poison argument arrives as poison.
* $`\mathsf{cond\_br}` (`condBr` in the Lean) takes an $`\mathsf{i1}`
  condition and has two successors. It jumps to the first when the
  condition is 1, and to the second when the condition is 0. Branching on
  poison is immediate UB.
* $`\mathsf{ret}~t^*` returns its operands, of the types $`t^*`, from the
  function: any number of them, each a value or poison
  (ADR-2026-10-29-2008).
* $`\mathsf{unreachable}` has no operands and no successors, and reaching
  it is immediate UB (ADR-2026-11-09-1548). A producer puts it where
  control never goes, such as after a call that never returns.

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

*Validation.* The grammar allows ops that no program may hold. Beyond the
types of each op's operands and results, which every dialect checks, the
{ref "The-fir-specification--Validation--Core-rules"}[core rules] of
validation ask:

* $`\mathsf{zext}_{M \to N}` and $`\mathsf{sext}_{M \to N}` strictly
  widen, with $`M < N`, and $`\mathsf{trunc}_{M \to N}` strictly narrows,
  with $`N < M`;
* $`\mathsf{ret}~t^*` returns the result types $`t^*` of its function;
* $`\mathsf{call}~f : t^* \to r^*` names a symbol $`f` to which the
  module's symbol table gives the function type $`t^* \to r^*`.

The other ops have no core rule of their own.
:::
