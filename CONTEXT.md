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
One operation of fir: a name, operands, attributes, result types, regions and
a location.
_Avoid_: instruction, node

**region**:
A body of blocks owned by a function or an op. In the core dialect a region is
a control-flow graph whose effectful ops run in the order of their position
in a block.

**block argument**:
A typed value that a block declares and that every branch to the block passes.
fir uses block arguments where LLVM uses phis.
_Avoid_: phi, phi node

**isolated from above**:
Said of a region whose ops use no value defined outside it. Every function
body is isolated from above.

**symbol reference**:
A reference to a function or other global by name, such as `@f` in `call @f`.
It is the only way to refer to a global.
_Avoid_: global value, use-list

**location**:
The required field on every op that says where the op came from: `unknown`, a
source range, a name, a call site, a fusion of locations, or derived from
another op.
_Avoid_: debug info, source position

**location table**:
The `locs { ... }` table that ends a module's text and gives the location that
each `@N` reference on an op stands for.
_Avoid_: debug table

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

### Semantics

**poison**:
fir's one deferred-UB value, produced for example when an `add nsw` overflows.
Using poison is not UB in itself, but some uses are, such as branching on it.
_Avoid_: undef (fir has none)

**freeze**:
The op that stops poison: `freeze` of poison yields an arbitrary but fixed
value, and every use of the result sees the same bits.

**immediate UB**:
Undefined behaviour at the moment an op runs, such as branching on poison or
dividing by zero. A source run with immediate UB allows any target behaviour.
_Avoid_: deferred UB (that is poison)

**outcome**:
How one run of a function ends: a value, poison, UB with a reason, or fuel
exhausted.

**observable behaviour**:
What a run of a function shows to the outside. In M0 it is the return value,
UB, or non-termination (fuel exhausted). Each dialect supplies its own
observations.
_Avoid_: result (a behaviour also covers UB and non-termination)

**refinement**:
The correctness relation: a target refines a source when each of its
observable behaviours is allowed by the source. Source UB allows anything, and
a poison result is refined by any value.
_Avoid_: equivalence

**fuel**:
The budget that bounds a run of the reference interpreter, so that every run
terminates. Running out of fuel stands for non-termination.

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
