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

:::moduleDocs (fingerprint := "11960897865273487084")
:::

:::readable Fir.Core.Op (pin := Fir.Core.Op.Valid) (fingerprint := "14685732944950056528")
*Ops.* An op of the core dialect carries the width $`N` of the integers it
works on, or the format $`\mathsf{float}\langle e,m \rangle` of the floats
it works on, so the types of its operands and results follow from it.
Below, $`c` is a constant of type $`\mathsf{i}N`, $`v` a vector of
$`1+e+m` bits, $`t` and $`r` are types, and $`f` is a function's symbol. The ops come in twenty families.

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
fma     \mathsf{fma}_{e,m}~\mathit{fmf}~r
```

* $`\mathit{fbin}_{e,m}` (`fbin` in the Lean) takes two values and
  $`\mathit{funary}_{e,m}` (`funary`) one, and each gives the model's
  result, rounded to nearest even where the op rounds.
* $`\mathsf{fma}_{e,m}` gives $`a \times b + c` of three values, rounded
  once.
* An op that rounds carries a rounding mode $`r`, in $`\mathit{fbin}` and
  $`\mathit{funary}` with its operation. Validation accepts only
  $`\mathsf{rne}`, and the model rounds to nearest even whatever the mode,
  since no valid module carries another.
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
sitofp,uitofp \mathsf{sitofp}_{N,e,m}~r \mid \mathsf{uitofp}_{N,e,m}~r
```

* $`\mathsf{sitofp}_{N,e,m}` reads an $`\mathsf{i}N` as a signed integer,
  and $`\mathsf{uitofp}_{N,e,m}` as an unsigned one, and each gives that
  integer as a value of $`\mathsf{float}\langle e,m \rangle`, rounded to
  nearest, ties to even, in Lean's float model. Each carries a rounding
  mode $`r`, of which validation accepts only $`\mathsf{rne}`. An integer too large for
  the format gives an infinity of its sign, and $`0` gives $`+0`. Neither
  is ever UB or gives a NaN, and a poison operand gives poison.

*Conversions between formats* give a float's number in another format
(ADR-2026-11-09-1549).

```grammar Fir.Core.Op
\mathit{op}
-             \dots
fpext,fptrunc \mathsf{fpext}_{e,m,e',m'} \mid \mathsf{fptrunc}_{e,m,e',m'}~r
```

* $`\mathsf{fpext}_{e,m,e',m'}` gives a value of
  $`\mathsf{float}\langle e,m \rangle` as a value of
  $`\mathsf{float}\langle e',m' \rangle`, a format that holds every value
  of it, with $`e \le e'` and $`m \le m'`, so it never rounds; and
  $`\mathsf{fptrunc}_{e,m,e',m'}` rounds it, to nearest, ties to even,
  into a format that cannot hold every value of it, with $`e' < e` or
  $`m' < m`. $`\mathsf{fptrunc}` carries a rounding mode $`r`, of which
  validation accepts only $`\mathsf{rne}`. The
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

*Field addresses* move a pointer to a field of an aggregate's layout
(#236).

```grammar Fir.Core.Op
\mathit{op}
-         \dots
fieldAddr \mathsf{fieldaddr}_{N}~s~j \mid \mathsf{fieldaddr}_{N,W}~s~j
```

* $`\mathsf{fieldaddr}_{N}~s~j` moves a pointer of
  $`\mathsf{ptr}\langle N \rangle` to the field $`j`, counted from 0, of
  the aggregate's layout with symbol $`s`: by the field's offset, which it
  reads in the layouts that the run gives every op.
  $`\mathsf{fieldaddr}_{N,W}~s~j` also takes an index of $`\mathsf{i}W`,
  read as signed, and moves the pointer to that element of a repeated
  field: by the field's offset plus the index times the element's units
  rounded up to its alignment. The move is $`\mathsf{ptradd}`'s: it keeps
  the provenance, and an index outside the field's elements is an address
  (ADR-2026-11-18-2041). It is never UB, and a poison operand gives
  poison.

*Addresses of globals* give a pointer to a global (#237).

```grammar Fir.Core.Op
\mathit{op}
-          \dots
globalAddr \mathsf{globaladdr}_{N}~s
```

* $`\mathsf{globaladdr}_{N}~s` gives a pointer of
  $`\mathsf{ptr}\langle N \rangle` to the first unit of the global $`s`.
  It is never UB and never gives poison.

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
  alignment that is a power of two no larger than $`2^{24} - 1`, and a
  valid type: an integer, a pointer or a float (#264); the count has no
  bound (ADR-2026-11-14-0915).

*Loads* read a value from memory (#231, #264).

```grammar Fir.Core.Op
\mathit{op}
-    \dots
load      \mathsf{load}_{N}~o~W~a
loadPtr   \mathsf{load}_{N}~o~\mathsf{ptr}\langle M \rangle~a
loadFloat \mathsf{load}_{N}~o~\mathsf{float}\langle e,m \rangle~a
```

* $`\mathsf{load}_{N}~o~W~a` loads an $`\mathsf{i}W` through a pointer of
  $`\mathsf{ptr}\langle N \rangle`, with the ordering $`o`, as an access
  aligned to $`a` units, or to the natural alignment of $`\mathsf{i}W` in
  memory $`N` when $`a` is none. Units that are not an integer's encoding,
  as fresh memory's, give poison. A poison pointer, and an access out of
  bounds, to a freed allocation, without provenance or misaligned, is
  immediate UB. The
  {ref "The-fir-specification--Validation--Core-rules"}[core rules]
  accept only the ordering $`\mathsf{nonatomic}` and an alignment that is
  a power of two no larger than $`2^{24} - 1`.
* $`\mathsf{load}_{N}~o~\mathsf{ptr}\langle M \rangle~a` (`loadPtr`)
  loads a pointer of memory $`M` in the same way. Only one such pointer's
  fragments, in order, give it; other units give poison (#231, Q3).
* $`\mathsf{load}_{N}~o~\mathsf{float}\langle e,m \rangle~a`
  (`loadFloat`) loads a float as $`\mathsf{load}_{N}~o~(1+e+m)~a` loads
  the integer of its width, and gives the float whose bit pattern that
  integer is: a NaN keeps its payload and sign.

*Stores* write a value to memory (#231, #264).

```grammar Fir.Core.Op
\mathit{op}
-     \dots
store      \mathsf{store}_{N}~o~W~a
storePtr   \mathsf{store}_{N}~o~\mathsf{ptr}\langle M \rangle~a
storeFloat \mathsf{store}_{N}~o~\mathsf{float}\langle e,m \rangle~a
```

* $`\mathsf{store}_{N}~o~W~a` stores an $`\mathsf{i}W` through a pointer
  of $`\mathsf{ptr}\langle N \rangle` and gives no result, aligned as a
  load of $`\mathsf{i}W` is. It writes the value's encoding, with zero bits
  past $`W`, or poison units for poison. A poison pointer, and an access
  that faults, is immediate UB. The core rules are those of a load.
* $`\mathsf{store}_{N}~o~\mathsf{ptr}\langle M \rangle~a` (`storePtr`)
  stores a pointer's fragments, or poison units, in the same way.
* $`\mathsf{store}_{N}~o~\mathsf{float}\langle e,m \rangle~a`
  (`storeFloat`) stores a float as $`\mathsf{store}_{N}~o~(1+e+m)~a`
  stores the integer of its bits.

*Copies and moves* carry units from one place of a memory to another
(#234; ADR-2026-11-09-1551; the human's rulings of 2026-11-18 on #234).

```grammar Fir.Core.Op
\mathit{op}
-       \dots
memCopy \mathsf{memcpy}_{N}~o~W \mid \mathsf{memmove}_{N}~o~W
```

* $`\mathsf{memcpy}_{N}~o~W` (`memCopy` of the kind $`\mathsf{copy}`)
  takes a destination and a source of $`\mathsf{ptr}\langle N \rangle` and
  a length of $`\mathsf{i}W`, read as unsigned, and carries that many units
  of the memory $`N` from the source to the destination, each exactly:
  bits, poison and pointer fragments alike, so a copied pointer keeps its
  provenance. It gives no result. A length of 0 does nothing, whatever the
  pointers are. Otherwise a poison pointer is immediate UB, and so are
  ranges that partly overlap, while equal ranges are allowed, and an
  access that faults. A poison length runs as some length, chosen, so it
  is UB wherever some length is.
* $`\mathsf{memmove}_{N}~o~W` (the kind $`\mathsf{move}`) does the same,
  and allows any overlap: it writes what the source held before it began.

*Fills* write copies of one unit (#234; the human's rulings of
2026-11-18 and 2026-11-19 on #234).

```grammar Fir.Core.Op
\mathit{op}
-      \dots
memSet \mathsf{memset}_{N}~o~V~W
```

* $`\mathsf{memset}_{N}~o~V~W` takes a destination of
  $`\mathsf{ptr}\langle N \rangle`, a value of $`\mathsf{i}V` and a length
  of $`\mathsf{i}W`, read as unsigned, and writes that many copies of the
  value's unit, poison units for poison, through the destination. The
  data layout asks that $`V` be the width of a unit of $`N`. Its pointer
  and its length are as $`\mathsf{memcpy}`'s.

The {ref "The-fir-specification--Validation--Core-rules"}[core rules]
accept only the ordering $`\mathsf{nonatomic}`.

*Pointers as integers* turn a pointer into the integer of its address and
back (#232; ADR-2026-11-09-1542).

```grammar Fir.Core.Op
\mathit{op}
-                    \dots
ptrExpose,ptrFromInt \mathsf{ptr\_expose}_{N,W} \mid \mathsf{ptr\_from\_int}_{N,W}
```

* $`\mathsf{ptr\_expose}_{N,W}` (`ptrExpose`) exposes the allocation of a
  pointer of $`\mathsf{ptr}\langle N \rangle` and gives its address as an
  $`\mathsf{i}W`. A poison pointer is immediate UB.
* $`\mathsf{ptr\_from\_int}_{N,W}` (`ptrFromInt`) turns an
  $`\mathsf{i}W` back into a pointer of $`\mathsf{ptr}\langle N \rangle`,
  into a live, exposed allocation that holds the address, or with no
  provenance. A poison integer gives poison.

The data layout asks that $`W` be the width of memory $`N`'s pointers,
and that memory $`N` be integral.

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
validation ask more of some ops: a width change strictly widens or
narrows, $`\mathsf{ret}` returns its function's result types,
$`\mathsf{call}` names a function of its type, a conversion between
formats goes the way its name says, the ops that round carry the mode
$`\mathsf{rne}`, the float ops carry no reserved word of their fast-math
flags, $`\mathsf{fieldaddr}` names a layout of its memory with the field
it asks, and $`\mathsf{globaladdr}` names a global of its own table in
its memory. $`\mathsf{alloca}`, the loads and the stores have the rules
given with them above, and the other ops have no core rule of their own.
:::
