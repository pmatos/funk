# Funk

Funk is a compiler toolchain whose intermediate representation, fir, has a
formal semantics in Lean. This glossary fixes the words that issues, ADRs, the
spec and the code use for fir's concepts. The decisions behind the terms are
the ADRs in [`docs/adrs/`](docs/adrs/).

## Language

### The IR

**funk**:
The toolchain: the Rust library and tools that parse, verify, transform and
compile fir, checked against the Lean semantics.

**fir**:
Funk's intermediate representation, written in lower case.
_Avoid_: FIR

**op**:
One operation of fir: a name, operands, attributes, result types, successors,
regions and a location. In Lean it is an `Operation`.
_Avoid_: instruction, node

**op instance**:
What a dialect gives for one op: its name, its attributes and the types it is
used at, such as `add` with `nsw` at `i32`. In Lean it is a value of the
dialect's `Op` type, from which the op's operand and result types follow.

**valid op instance**:
An op instance whose operand and result types validation accepts
(`TypesValid`), such as `udiv` at `i8` but not at `i0`. Every op of a
valid function is one. The poison obligations speak only of valid op
instances (ADR-2026-11-02-1515).

**attribute**:
A constant part of an op that is not a value, such as the flag `nsw`, the
predicate `slt` of an `icmp`, the value of a `const` or the callee `@f` of a
`call`. Attributes and types are written as generic terms, so a new dialect
needs no new syntax.

**successor**:
A block that a terminator may jump to, together with the values it passes to
that block's arguments, as in `br ^loop(%i1, %acc1)`.

**terminator**:
The op that ends a block and says where control goes next: to one of its
successors, or back to the caller. In the core dialect: `br`, `cond_br` and
`ret`.

**region**:
A body of blocks owned by a function or an op. In the core dialect a region is
a control-flow graph whose effectful ops run in the order of their position
in a block.

**block argument**:
A typed value that a block declares and that every branch to the block passes.
fir uses block arguments where LLVM uses phis.
_Avoid_: phi, phi node

**entry block**:
The first block of a region. A function's parameters are the arguments of its
entry block, and no branch may jump to it.

**reachable block**:
A block that some path of branches from the entry reaches. Every block of a
valid function is reachable; producers delete the others before validation.
_Avoid_: dead block (say unreachable block)

**item**:
A top-level entry of a module, such as a function. Every item is written
`kind @sym(params) -> results attrs { body }`. M0 has one kind, `func`;
nested modules and globals would be other kinds, with the same syntax.

**isolated from above**:
Said of a region whose ops use no value defined outside it. Every function
body is isolated from above.

**symbol reference**:
A reference to a function or other global by name, such as `@f` in `call @f`.
It is the only way to refer to a global. A name that is not a word is
quoted, as in `@"1"`.
_Avoid_: global value, use-list

**location**:
The required field on every op that says where the op came from: `unknown`, a
source range such as `"f.c":2:3 to 2:14` (end exclusive, columns in UTF-8
bytes), a name, a call site, a fusion of locations, or derived from another
op.
_Avoid_: debug info, source position

**location reference**:
The number that an op holds for its location, written `@N` at the end of the
op. `@1` is always a location reference: the symbol named `1` is written
`@"1"`.

**location table**:
The `locs { ... }` table that ends a module's text and gives the location that
each `@N` reference on an op stands for.
_Avoid_: debug table

**verdict**:
What a tool says about a text: accepted, rejected by the parser (a parse
error, with a text position), or rejected by validation (a validation
error, with an IR location). `funk verify` and `fir-ref validate` must give
the same verdict on every text.

**validation check**:
The executable check, in the spec, that decides validation: it lists a
module's problems, each a broken rule said in words with where it is, and
the list is empty exactly when the module is valid. `fir-ref validate` runs
it; `funk verify` is the Rust verifier that must agree with it.

**well-formed module**:
A module whose printed text says everything it holds, so that parsing the
text gives the module back. Every valid module is well formed. A text that
follows the grammar but does not decode, such as one with a type mismatch,
is a parse error with a located reason.

### Native calls

**funk calling convention**:
The rules for calling a function compiled by funk: where its arguments and
results pass, which registers it preserves, how its symbol is spelled, and
how its stack is aligned. A call between funk functions passes arguments
without extension; calls to code funk did not compile may need other rules.

**result area**:
Stack space in a caller's frame where a callee writes its results when
they take more than the two registers `%rax` and `%rdx`. The caller passes
its address as the call's first argument (ADR-2026-11-03-0109). It is
backend stack space, like a slot, not fir memory.
_Avoid_: return buffer, sret

### Dialects

**dialect**:
A named set of ops and types, with their rules, from which fir is built. How
dialects and extensions are defined (H4, H5) is not decided yet.

**core dialect**:
The small, CPU-shaped dialect that M0 defines: the integer types `iN`, the
float types, the pointer types `ptr<N>` and the M0 op set.
_Avoid_: base fir, core IR

**extension dialect**:
A dialect other than the core dialect, such as one for a GPU or a quantum
processor. Extension dialects are how fir reaches new hardware.

**op registry**:
The table through which `funk-ir` checks generic ops: each dialect registers
its ops, and the verifier checks every op against its registration.
_Avoid_: op enum

**test dialect**:
A dialect that only tests register, to show that a new dialect needs no
change to the IR, the parser or the printer. Its ops and types are named
`toy.` and a word, such as `toy.br`, so they never collide with core ops.

**sum dialect**:
One dialect that holds the ops of two dialects over the same types, so that
one module can mix them. It sends each op name to one of the two, so no op
name may belong to both. Only the Lean tests build one, from the core
dialect and a test extension over it (ADR-2026-11-09-2306).

### Semantics

**poison**:
fir's one deferred-UB value, produced for example when an `add nsw` overflows.
A poison operand gives a poison result unless the op says otherwise. Using
poison is not UB in itself, but some uses are: branching on it (S1), and any
use where some value it could take would be UB, such as dividing by it, or
dividing it by `-1` with `sdiv` or `srem`, since it could be the signed
minimum. A program writes a poison value with the core op `poison`, as
in `%p: i32 = poison` (ADR-2026-11-03-1615).
_Avoid_: undef (fir has none)

**poison class**:
How an op treats a poison operand. A propagating op returns only poison from
it, and is UB on it only where a defined value in its place could be UB too;
it also returns a result on some operands with no poison, and proves all
three in Lean. An exception, such as `select` or `freeze`, states its own
rule. Every op of every dialect declares its class. The obligations speak
of valid op instances, and every one that runs by its own rule, a
terminator or an op with no callee, is total and monotone: refining its
operands refines what it does (ADR-2026-11-02-1514,
ADR-2026-11-02-1515).

**freeze**:
The op that stops poison: `freeze` of poison yields an arbitrary but fixed
value, and every use of the result sees the same bits.

**immediate UB**:
Undefined behaviour at the moment an op runs, such as branching on poison or
dividing by zero. A source run with immediate UB allows any target behaviour.
_Avoid_: deferred UB (that is poison)

**outcome**:
How one run of a function ends: it returns an observation, hits UB with a
reason, or runs out of fuel. For a function that returns one `iN`, the
outcomes are a value, poison, UB with a reason, or fuel exhausted. A function
may return any number of values.

**stuck run**:
A run of the interpreter on an invalid module with a path that reaches a
case validation rules out, such as an undefined value. That path ends stuck,
an error outside the outcomes, never UB. Stuck is per path, since it can
depend on choices. No path of a valid module's runs is ever stuck.

**observation**:
What an observer sees of a run that returns. Each dialect supplies its
observations and how they refine. In M0 it is the list of returned values,
each a value or poison.

**observable behaviour**:
What the runs of a function show to the outside, over every fuel budget. In
M0 it is the returned values, UB, or divergence. Each dialect supplies its
own observations.
_Avoid_: result (a behaviour also covers UB and divergence)

**divergence**:
A run that never ends: it runs out of fuel at every budget. Running out of
fuel at one budget is not divergence.
_Avoid_: fuel exhausted (for divergence)

**refinement**:
The correctness relation: a target refines a source when each of its
observable behaviours is allowed by the source. Source UB allows anything, and
a poison result is refined by any value. A target function refines a source
function when, on every argument vector, poison included, its behaviour
refines the source's.
_Avoid_: equivalence

**fuel**:
The budget that bounds a run of the reference interpreter, so that every run
terminates. Every op takes one step, and a callee runs on the steps its
caller has left, so a call and its callees share one budget. A run that runs
out of fuel at every budget diverges.

**call effect**:
How a call runs: the interpreter finds the callee in the module by its
symbol, runs it with the fuel the caller has left, and binds what it returns
to the call's results. A dialect only says which of its ops call which
function.

**execution rules**:
What an op does when it runs: the results it gives, the UB it hits, or where
a terminator sends control. Each op family of the core dialect has them
in Lean, so every core op does, `call` through its callee's run. An op
without them has no outcome in the spec
([fir-ref.md](docs/decisions/fir-ref.md#an-op-without-rules)), and
`fir-ref run` reports such an op as an error, never as a result.

**fuel monotonicity**:
The interpreter's obligation that more fuel never changes how a run that
returns or hits UB ends. It lets one run, at a budget that does not run out,
stand for the function's observable behaviour.

**progress**:
The interpreter's obligation that a run of a valid function has some outcome
at every fuel budget. Without it, an empty behaviour would refine anything.

**no-stuck obligation**:
The interpreter's obligation that no path of a run of a valid function is
stuck, at any fuel budget. With every op that runs by its own rule total,
and with an interpreter whose own steps never drop a path, as its
definition ensures, no path of the run is lost.

**op totality**:
The obligation of every valid op instance that runs by its own rule, a
terminator or an op with no callee, to have an outcome on every operand
vector: a result or UB, or for a terminator, where control goes or UB. So
its semantics never drops a path of a run. An op with a callee, such as
`call`, has no rule of its own: its meaning is its callee's run.

**op monotonicity**:
The obligation of every valid op instance that runs by its own rule that
refining its operands refines what it does. It makes refinement
compositional: a part replaced by one that refines it refines the whole
function. Refinement asks it only of the ops a run can reach, so for a
valid module the valid instances are enough (ADR-2026-11-05-1715).

### The oracle

**reference interpreter (`fir-ref`)**:
The Lean interpreter that defines fir's semantics, built as the `fir-ref`
executable. It is a test oracle for development and CI, and never ships inside
a compiler.
_Avoid_: emulator, simulator, Rust interpreter

**choice sequence**:
The values that a run picks, in order, each time it freezes poison. Given one,
a run of the reference interpreter has one outcome.

**exhaustive mode**:
The `fir-ref` mode that tries every choice sequence, within a budget on the
total number of choice bits, and prints the set of outcomes.

**scripted mode**:
The `fir-ref` mode that takes one choice sequence and prints one outcome. A
sequence that does not fit the run, with too few or too many values or a
value that is not of its choice's type, is an error, never an outcome.

**sampled mode**:
The `fir-ref` mode that draws each choice from a generator seeded with a
number, as the run makes it, and prints one outcome and the values it
drew: a choice sequence that fits the run.

**choice budget**:
The most bits that one path may choose in exhaustive mode. A run that would
choose more gives no set of outcomes: exhaustive mode says that the budget
is exceeded.

**choice tree**:
The monad that `fir-ref` runs the interpreter in: a tree whose nodes are
choices and whose leaves say how each path ends. It maps to the set monad
of the spec, so its walks, exhaustive, scripted and sampled, are proved
sound.

**declared results**:
The allowed results that a test lists, each with a witness choice sequence
from which scripted mode reproduces it. When the run chooses more than the
choice budget, seeded runs of sampled mode check that it gives no other.

**differential test**:
A test that runs a module on `fir-ref` and as native code, and checks that the
native result refines the `fir-ref` result.

**judgement**:
How the harness classifies a test: passed, failed or invalid, with a reason.
A differential test passes when native results refine the reference outcomes;
an interpreter-only test passes when its outcome matches what it expects.
An invalid test proves nothing and never counts as a pass.
_Avoid_: verdict (a verdict says whether a text parses and validates)

**poison stand-in**:
A defined value of `iN` that native code runs a differential test on in
place of a poison argument: one of the type's boundary bit patterns, 0, 1,
all ones, the signed minimum or the signed maximum
([fir-ref.md](docs/decisions/fir-ref.md#poison-arguments)).
_Avoid_: stand-in alone (the spec's prose also uses it for a placeholder
rule of an op, and `test_main.py` for a fake tool)

**invalid test**:
A differential test that can prove nothing: an outcome in its set is UB or
fuel exhausted, or its choices exceed the budget and it declares no results.
It never counts as a pass.

**interpreter-only test**:
A test that runs on `fir-ref` only, and states the result it must give, on
the path that its choices name: the returned values, UB or fuel exhausted.
It covers what native code cannot check, such as UB, fuel exhaustion and
widths the backend does not lower.

**must-reject text**:
A text of the test corpus that breaks one rule, and that `funk verify` and
`fir-ref validate` must both reject with the same verdict: rejected by the
parser or by validation. When the ops of the core dialect cannot break a
rule alone, such as the scope of a value defined in a region, the text
breaks a second rule too, and names both (ADR-2026-10-30-2050).
