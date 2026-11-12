# Current decisions: semantics

This page says what holds today about the meaning of fir. It is the record: when
this page and an ADR disagree, the page wins, and the ADR is fixed or deleted
(ADR-2026-11-09-1610). See semantics-m1-design.md for the M1 design not built
yet, semantics-m1-trace.md for what an M1 run shows, semantics-poison.md for
poison, UB and `freeze`, semantics-dialects.md for sums, semantics-effects.md
for op effects, and semantics-floats.md for floating point.

## Ground rule: fir reaches any hardware

fir must be able to reach any kind of hardware. CPUs come first. GPUs, NPUs,
TPUs and hardware we cannot predict yet, such as photonic or quantum
processors, are targets too. The core stays a small CPU-shaped dialect. Other
targets come in as extension dialects. The openness lives in how fir is built,
not in what the core contains. No milestone targets non-CPU hardware yet.
This rule is G0, and it is a standing check. Every decision is checked against
it, and none may close that door (ADR-2026-10-29-2016).

Types and ops come from dialects, so there is no closed core enum. The core's
`iN`, `float<e,m>` and `ptr` are one dialect's types. One text grammar covers every
dialect, so a new dialect needs no parser change. The Lean semantics is
parameterized over the dialect. Ops, types and effects come in through
typeclasses. Lean proofs are stated over the dialect parameter where they can
be (ADR-2026-10-29-2016).

`funk-ir` holds an op as generic data: results, name, attributes, operands,
successors, regions and a location. A registry checks it, and each dialect
registers its ops there. Types are extensible the same way
(ADR-2026-10-30-1146).

G0 shaped the later decisions. Memory has several typed memories
(ADR-2026-11-09-1542). Dialects add types and attributes, not only ops
(ADR-2026-11-09-1543). A dialect need not lower to core (ADR-2026-11-09-1544).
The verifier has a hook for use-once values, which quantum dialects require
(ADR-2026-10-29-2016, ADR-2026-11-09-2257).

Generic code sees every op alike and must not know the ops of any dialect. It
reaches a dialect's ops only through the registry or the dialect's classes.
Generic code is most of `funk-ir` and of the Lean spec. Code that builds, lowers
or runs one dialect's programs may name its ops. That code is the dialect's own
files, the x86-64 backend and the command lines of `funk` and `fir-ref`. It is
also the tests and the corpus. The grammar's own words, such as `func`, are not per-op code
(ADR-2026-11-03-0600).

CI keeps this line. `crates/funk-ir/tests/g0.rs` and `scripts/check_g0.py` fail
on per-op code in generic code. `lean/FirTest/G0.lean` breaks when generic code
narrows to the core dialect. Each check covers a
place unless the line excludes it, so a new file is checked
(ADR-2026-11-03-0600).

A word that names a core op is a word of the core dialect, whatever else it
means. Generic code does not write such a word alone as a string. It names the
concept with the spec's own definitions, such as `PoisonOr.poison`. A string
that holds the word among other text stays allowed. Neither check has a list of
exempt words (ADR-2026-11-03-1617).

## Program structure

fir is a CFG: a function body is a graph of blocks, linked by branches. It is
not a sea of nodes and not an RVSDG. Effectful ops are ordered by their
position in a block. An earlier op's effects happen before a later op's. A pass
that moves an effectful op must keep every effect order the source fixes
(ADR-2026-10-29-2005).

This order binds the core dialect. Extension dialects may define other region
kinds, such as unordered dataflow regions. The format admits them, and M1 builds
none (ADR-2026-11-09-1543). Explicit memory tokens may come later as a stricter
mode (ADR-2026-10-29-2005).

fir is in SSA form, with block arguments and no phis. A block declares typed
arguments. A branch passes one value per argument of its target. Both `br` and
`cond_br` pass block arguments. The verifier checks the count and the types at
every branch (ADR-2026-10-29-2010).

A function is a region isolated from above. Nothing in one function references
a value of another function. Functions reach each other only by symbol
(ADR-2026-10-29-2011).

An op refers to a function or other global by symbol only, as in `call @f`.
Constants are ordinary ops inside the function, not module-level values. The
IR keeps no module-wide use-lists. The verifier resolves every symbol reference
(ADR-2026-10-29-2012). Symbol tables must be able to nest. M0 does not use
nested modules, but its data structures must not rule them out
(ADR-2026-10-29-2016). M1 designs global items and function addresses
(ADR-2026-11-09-1546, ADR-2026-11-09-1548) and `module` items
(ADR-2026-11-09-1543).

fir has no nesting limit. Every text the grammar accepts is read at any depth,
and the IR holds any depth. Every tool, in Rust and in Lean, handles any depth
on a small stack. Memory bounds how deep a text
can go, not the stack. No tool relies on a large reserved stack
(ADR-2026-10-30-1549).

## Integers and numbers

fir integer types are bitvectors `iN`. Signedness lives on ops, never on types.
Every op whose meaning depends on sign comes in a signed and an unsigned form,
such as `sdiv` and `udiv`. Pointer types are separate: `ptr<N>` points into the
memory `N`, and the core `ptr` is `ptr<0>`. A value of a pointer type is poison
or a pointer, and no op makes or uses one yet (ADR-2026-11-09-1542). These types
belong to the core dialect, not to a closed type system (ADR-2026-10-29-2007).

An integer type `iN` has `1 <= N <= 16,777,215`, which is `2^24 - 1`. The IR
and the Lean interpreter accept every width in that range. A wider type does
not decode, in Lean and in Rust alike. A frontend that needs a wider integer
has to split it (ADR-2026-11-03-1000). A float type `float<e,m>` is no wider
than that in all, and semantics-floats.md says which formats the core takes
(ADR-2026-11-11-0950).

Every other number that gives the text its structure is below `2^32`: a
location reference, a line and a column. An integer attribute has no bound of
its own. The dialect that reads it bounds it, as a core constant must fit its
type. A number out of its range is a parse error, located at the number
(ADR-2026-11-03-1000).

The M0 backend supports `i1`, `i8`, `i16`, `i32`, `i64` and `i128`. `i128`
lowers to register pairs, with division through a runtime helper. The backend
rejects any other width with a clear diagnostic. Odd widths, such as `i7` and
`i33`, are tested on the interpreter only (ADR-2026-10-29-2007).

## Refinement

A target is correct if each of its observable behaviours is allowed by the
source. Source UB allows any target that first shows the source's events before
the UB (ADR-2026-11-09-1540). A poison result is refined by any value.
Refinement is defined over a domain of observations that the semantics
supplies. Each dialect supplies its observations (ADR-2026-10-29-2008).

Core functions, `ret` and `call` have any number of results, none included. No
validation rule limits them. What a returning run shows is the list of its
returned values, each a value or poison. That list is M0's observation
(`Core.Obs`), and refinement compares it value by value. `fir-ref`'s output,
the harness's expected results and declared results are lists of values
(ADR-2026-10-30-0816).

In M0, a function's observable behaviour is its returned values, UB, or
non-termination (fuel exhausted). The full definition also counts calls to
external symbols and reachable memory. M0 has no memory, and every M0 callee is
inside the module. The one exception is the `i128` division helper, which is
tested on its own. M1 makes observable behaviour a trace judged for each world
(ADR-2026-11-09-1540). The relation stays the same (ADR-2026-10-29-2008).

The differential harness compares a native result with the `fir-ref` result by
refinement. A poison result from `fir-ref` matches any native value. A test
whose `fir-ref` result is UB is invalid, never a pass. Any later check, such as
per-compile refinement checking (S8, not decided), checks this relation and no
other (ADR-2026-10-29-2008).

Monotonicity makes refinement compositional. Replacing one part of a function
with a part that refines it refines the whole function (ADR-2026-10-30-0818).

The core dialect's behaviour is a set of outcomes. Its refinement is set
refinement: each outcome of the target is allowed by some outcome of the
source. The theorems about behaviour and refinement in `lean/Fir` are about
this set instance (ADR-2026-11-09-1322).

The seam for other behaviour models has two parts. The interpreter is generic
over its monad: `Func.run` takes any monad `m` with `DialectDenote d m`. The
tree of choices maps to a meaning by a monad morphism. `Func.run_map` carries
any such morphism to the interpreter's run (ADR-2026-11-09-1322).

A dialect that needs probabilistic behaviour supplies its own model. A model is
an interpretation of the tree, or of the tree extended with the dialect's own
effect, as a `MonadMorphism`. It comes with a refinement order on that model.
On the outcomes a model gives with non-zero weight, its order must imply set
refinement. So results proved for the set instance stay valid as statements
about which outcomes are possible. They say nothing about how likely an outcome
is (ADR-2026-11-09-1322).

A behaviour-model class with `SetM` as one instance is deferred. It waits for a
real probabilistic dialect to give a second instance to design against. Passing
set refinement does not show that a target keeps a distribution.
`lean/FirTest/G0.lean` tests the seam with a toy tree of weighted choices
(ADR-2026-11-09-1322).

The refinement engine asks monotonicity only of the ops a run can reach. Those
are the ops of the source module's functions and of the function that runs. A
lawful dialect gets both function-level refinement theorems for valid modules
from the class alone. `Core.args_isRefinedBy` holds for every core module, valid
or not (ADR-2026-11-05-1715).

Replacing a callee is replacing a body. Every function keeps its symbol, its
parameters and its result types. Congruence assumes that the new `@g`, run in
the new module, refines the old `@g`, run in the old. It concludes the same
relation for every function of the module (ADR-2026-11-02-1350). It needs
nothing of the new body, because a call of `@g` is a black box
(ADR-2026-11-05-1715).

`Func.runs_replaceBody_isRefinedBy` asks that the parameter types of `@g` have
finitely many argument vectors. A dialect with a type of infinitely many values
cannot use the general theorem as it is. Refined arguments need no finiteness
(ADR-2026-11-02-1426). `ptr` has values now, infinitely many, so the core's
congruence is restated for a callee with no pointer parameter, and #214 proves
it for the rest (ADR-2026-11-09-1542).

Runs with memory refine too, whatever their ops do to the memories. A poison
unit of memory is refined by any unit, and every other unit only by itself;
refined memories have the same frames and allocations, and the units of a
freed block are not compared. A dialect lawful in
its monotonicity (`LawfulDialectMonotone`) has each op monotone over its
semantics with memory, from memories that refine others. Refinement then
compares runs from given memories, the end memories included, since a
callee runs from its caller's memories. Refined arguments and memories need
nothing more. Congruence assumes the new callee refines the old from every
memories, and one fuel bound for it, until #214. These proofs stand beside
those in the set monad. The relation on end memories is a proof device for
composing calls, stricter than the observation of ADR-2026-11-09-1540; #233
reconciles them (ADR-2026-11-11-1002).

## The interpreter and its calculus

fir's semantics is a monadic definitional interpreter, written in Lean. It is
not built on interaction trees. Fuel bounds every run, so the interpreter always
terminates. A run that uses all its fuel ends with fuel exhausted. Fuel
exhaustion is an outcome of its own, beside a value, poison and UB. It stands
for non-termination (ADR-2026-10-29-2009).

It is the only interpreter: a test oracle for development and CI, run as
`fir-ref`. It never ships inside a compiler. Lean holds the semantics, the
interpreter and its own `.fir` parser and printer. Rust holds the whole
toolchain: the IR library, verifier, passes, backends and driver. There is no
Rust interpreter in M0. One may come later only as a copy tested against Lean,
never as the definition (ADR-2026-10-29-2009).

fir's Lean semantics is its own calculus. It takes no dependency on LeanMLIR,
and keeps LeanMLIR's shape wherever that is cheap (ADR-2026-10-29-2030):

- A dialect is a structure with `Op` and `Ty`.
- `TyDenote` gives each type its meaning.
- `DialectSignature` gives each op its operand and result types.
- Each op's semantics has the shape of LeanMLIR's `DialectDenote.denote`.
- Values of `iN` are `PoisonOr (BitVec N)`, fir's own type.
- Refinement is written through a heterogeneous class shaped like LeanMLIR's
  `HRefinement`. That fixes only the notation.

It differs from LeanMLIR on purpose in four places (ADR-2026-10-29-2030):

- Terms are extrinsically typed. Values have names, every op has a location,
  and a function is a CFG of blocks with arguments and successors. Typing is a
  separate validation judgement.
- Terminators are ops that `DialectSignature.isTerminator` marks. Their
  semantics is `DialectDenote.exit`, which returns an `Exit`: a successor
  index, or return.
- A dialect does not fix one monad. Its semantics states the effects it needs
  as class constraints on the monad, such as `choose w` and immediate UB.
- The parser and printer are fir's own, over the extrinsic syntax.

Memory is an effect of a run. The state layer `StateT` over the way of
computing carries the memories of a run, and the interpreter runs every
function in a frame, which frees the function's stack allocations when it
returns. In a monad with no memory, such as the set monad or the tree of
choices, a frame changes nothing, so M0's runs are unchanged
(ADR-2026-11-10-2350). A function's runs with memory run its dialect's
semantics with memory at a naming of the memories, from the empty
memories. They are fuel-monotone for every dialect, and for a dialect that
lifts the set monad they are its runs (ADR-2026-11-11-0623).

Runs with memory have progress for every dialect, whatever its ops do to the
memories. No path is stuck when every function of the module is valid and
runs within it with memory, at the run's naming (`Func.InModuleAt`, which
states the rules for terminators over their exits from any memories). Each
run has an outcome at every budget when the dialect is also lawful in its
totality (`LawfulDialectTotal`): each op that runs by its own rule has an
outcome from any memories, at every naming. That class asks for no semantics
in the set monad. A dialect that lifts the set monad and is lawful meets it,
and so do sums and lifts whose sides do. A valid core module meets both
(`Core.memNeverStuck`, `Core.memProgress`). These proofs stand beside those
for runs in the set monad, step by step; deriving one from the other is a
later refactor over fuel monotonicity, progress and refinement together
(ADR-2026-11-11-0801).

The term carries op regions from M0 on, empty for core ops. Kinds and rules
of regions: ADR-2026-11-10-1941. The CFG is the core dialect's region kind.
Extensions compose as ADR-2026-11-09-1543 and ADR-2026-11-09-1544 say. Verified
rewrites (M2) mean fir's own refinement-based rewrite framework, or VeIR if S7
is reopened (ADR-2026-10-29-2030).

## Calls and fuel

A call has no op-level rule. Its meaning is its callee's run. A dialect names
the function that an op calls through `DialectCall` (`callee?`). The interpreter
runs that op, not its `denote`. It finds the callee in the module by symbol and
passes the op's operands as arguments. It binds the callee's returned values to
the op's results. A run belongs to a module: `Func.runOps` and `Func.run` take
the module whose functions calls run. The call effect is the run's, and it is
not a class constraint on the monad (ADR-2026-11-02-0836).

`call` has no entry in `Core.Op.denote?`, so its `denote` has no outcome in the
set monad. The interpreter never reaches it. Where the spec counts which ops
have rules, an op with a callee has them. A statement proved op by op must leave
out the ops with a callee. M2's rewrite rules need the same exclusion, tracked
by #96 (ADR-2026-11-02-1514).

Fuel stays the interpreter's argument, not state in the monad. Every op takes
one step, a call included. `Func.runOps` returns the steps it leaves with the
values it returns. A callee gets the steps its caller has left after the call's
step. The caller goes on with the steps that the callee gives back. A callee
that runs out of fuel ends the run so. Its UB and stuck paths are its caller's
(ADR-2026-11-02-0836).

The recursion is well-founded on the budget, not structural. Nothing is
`partial`. Fuel is a device of the Lean definitions. It must not change what a
program means, nor any result of `fir-ref`. Fuel monotonicity holds for every
function of every module, calls included, since only the interpreter counts
fuel (ADR-2026-11-02-0836).

## Stuck paths and proofs

A terminator may have results in the generic spec, but a run never binds them.
Validation has no rule that a terminator has no results, and `Exit` carries no
values. So "a terminator that jumps gives no results" is a condition that each
dialect meets for its own terminators. Validation does not check it
(ADR-2026-11-02-2248).

The generic progress and no-stuck theorems cover a function only through that
condition. So "a validated module never gets stuck" holds only for a dialect
whose terminators meet it. The core dialect meets it. No path of a run of a
function of a valid core module is stuck (`Core.neverStuck`). `Exit` does not
grow in M0. M4's design of exceptions and unwinding chooses between a validation
rule and values on `Exit` (ADR-2026-11-02-2248).

`fir-ref run` walks a machine with explicit call frames. The machine is proved
equal to the spec's interpreter
([fir-ref-fast-paths.md](fir-ref-fast-paths.md#running)).

The core law files have no use for `bv_decide` today. `bitVec_one_cases` is
proved by `revert v; decide`. The two proofs at symbolic width stay as they are,
because `bv_decide` needs a width that is a literal. `bv_decide` remains the
tool that the roadmap names as the bar for admitting rewrite rules
(ADR-2026-11-09-1315).
