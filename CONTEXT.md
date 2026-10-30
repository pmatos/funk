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

### Dialects

**dialect**:
A named set of ops and types, with their rules, from which fir is built. How
dialects and extensions are defined (H4, H5) is not decided yet.

**core dialect**:
The small, CPU-shaped dialect that M0 defines: the integer types `iN`, the
reserved `ptr` type and the M0 op set.
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
dialect and a test dialect (ADR-2026-10-30-2040).

### Semantics

**poison**:
fir's one deferred-UB value, produced for example when an `add nsw` overflows.
A poison operand gives a poison result unless the op says otherwise. Using
poison is not UB in itself, but some uses are: branching on it (S1), and any
use where some value it could take would be UB, such as dividing by it, or
dividing it by `-1` with `sdiv` or `srem`, since it could be the signed
minimum.
_Avoid_: undef (fir has none)

**poison class**:
How an op treats a poison operand. A propagating op returns only poison from
it, and is UB on it only where a defined value in its place could be UB too;
it also returns a result on some operands with no poison, and proves all
three in Lean. An exception, such as `select` or `freeze`, states its own
rule. Every op of every dialect declares its class, and every op is total
and monotone: refining its operands refines what it does.

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
terminates. A run that runs out of fuel at every budget diverges.

**execution rules**:
What an op does when it runs: the results it gives, the UB it hits, or where
a terminator sends control. Each op family's ticket writes them in Lean.
Until it does, the family's ops have none: the spec gives them no outcome,
and `fir-ref run` reports such an op as an error, never as a result.

**fuel monotonicity**:
The interpreter's obligation that more fuel never changes how a run that
returns or hits UB ends. It lets one run, at a budget that does not run out,
stand for the function's observable behaviour.

**progress**:
The interpreter's obligation that a run of a valid function has some outcome
at every fuel budget. Without it, an empty behaviour would refine anything.

**no-stuck obligation**:
The interpreter's obligation that no path of a run of a valid function is
stuck, at any fuel budget. With every op total, and with an interpreter
whose own steps never drop a path, which #10's definition must ensure, no
path of the run is lost.

**op totality**:
Every op's obligation to have an outcome on every operand vector: a result
or UB, or for a terminator, where control goes or UB. So its semantics never
drops a path of a run.

**op monotonicity**:
Every op's obligation that refining its operands refines what it does. It
makes refinement compositional: a part replaced by one that refines it
refines the whole function.

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
The `fir-ref` mode that takes one choice sequence and prints one outcome.

**declared results**:
The allowed results that a test lists, each with a witness choice sequence
from which scripted mode reproduces it.

**differential test**:
A test that runs a module on `fir-ref` and as native code, and checks that the
native result refines the `fir-ref` result.

**invalid test**:
A differential test that can prove nothing: an outcome in its set is UB, or its
choices exceed the budget and it declares no results. It never counts as a
pass.
