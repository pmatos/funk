# Current decisions: semantics

This page says what holds today about the meaning of fir. It is the record: when
this page and an ADR disagree, the page wins, and the ADR is fixed or deleted
(ADR-2026-11-09-1610). It continues on these pages:

- semantics-refinement.md: what correctness means, behaviour models and the
  refinement theorems;
- semantics-interpreter.md: the Lean interpreter, its calculus, calls, fuel and
  stuck paths;
- semantics-poison.md: poison, UB and `freeze`;
- semantics-dialects.md: how dialects extend fir, and sums;
- semantics-effects.md: op effects;
- semantics-floats.md: floating point;
- semantics-m1-design.md: the M1 design, most of it not built yet;
- semantics-m1-dialects.md: dialects, levels and the second dialect in M1;
- semantics-m1-trace.md: what an M1 run shows.

The rows of the fir v0 decision record (E0, S2, H1, H2 and H3 on this page, S4
on semantics-refinement.md and S7 on semantics-interpreter.md) were agreed with
the human on 2026-10-29 and are stated in the M0 epic, #5.

## Ground rule: fir reaches any hardware

fir must be able to reach any kind of hardware. CPUs come first. GPUs, NPUs,
TPUs and hardware we cannot predict yet, such as photonic or quantum
processors, are targets too. The core stays a small CPU-shaped dialect. Other
targets come in as extension dialects. The openness lives in how fir is built,
not in what the core contains. No milestone targets non-CPU hardware yet.
This rule is G0, and it is a standing check. Every decision is checked against
it, and none may close that door (ADR-2026-10-29-2016). The human set G0 on
2026-10-29 (#5). Rejected: a closed core, such as a Rust `enum` of core ops or a
grammar with one production per op, which is costly to open once code depends
on it.

Types and ops come from dialects, so there is no closed core enum. The core's
`iN`, `float<e,m>` and `ptr` are one dialect's types. One text grammar covers
every dialect, so a new dialect needs no parser change. The Lean semantics is
parameterized over the dialect. Ops, types and effects come in through
typeclasses. Lean proofs are stated over the dialect parameter where they can
be, so a new dialect does not reopen them. Checks that a closed `enum` would
give for free, such as an op's operand count, live in the registry and the
verifier (ADR-2026-10-29-2016).

`funk-ir` holds an op as generic data: results, name, attributes, operands,
successors, regions and a location. A registry checks it, and each dialect
registers its ops there. Types are extensible the same way
(ADR-2026-10-30-1146).

G0 shaped the later decisions. Memory has several typed memories
(ADR-2026-11-09-1542). Dialects add types and attributes, not only ops
(ADR-2026-11-09-1543). A dialect need not lower to core (ADR-2026-11-09-1544).
The verifier has a hook for use-once values, which quantum dialects require
(ADR-2026-10-29-2016, ADR-2026-11-09-2257). A dialect that needs probabilistic
behaviour supplies its own behaviour model (ADR-2026-11-09-1322).

Generic code sees every op alike and must not know the ops of any dialect. It
reaches a dialect's ops only through the registry or the dialect's classes.
Generic code is most of `funk-ir` and of the Lean spec. Code that builds, lowers
or runs one dialect's programs may name its ops. That code is the dialect's own
files, the x86-64 backend and the command lines of `funk` and `fir-ref`. It is
also the tests and the corpus. The grammar's own words, such as `func`, are not
per-op code (ADR-2026-11-03-0600).

CI keeps this line. `crates/funk-ir/tests/g0.rs` and `scripts/check_g0.py` fail
on per-op code in generic code. `lean/FirTest/G0.lean` breaks when generic code
narrows to the core dialect. Each check covers a
place unless the line excludes it, so a new file is checked. Moving the line
edits ADR-2026-11-03-0600 in place (ADR-2026-11-03-0600). Rejected: review by
hand, which does not last, and Lean theorems alone, since a generic definition
could test an op's name as a string and keep every theorem true.

A word that names a core op is a word of the core dialect, whatever else it
means. Generic code does not write such a word alone as a string. It names the
concept with the spec's own definitions, such as `PoisonOr.poison` and
`TyPoison.IsPoison`, and leaves the spelling to code that may name core ops:
`fir-ref`'s command line spells a poison value `poison`. A string that holds
the word among other text, such as a message, stays allowed. Neither check has
a list of exempt words: both take `poison` from the dialect, as they take every
op's name. `scripts/test_check_g0.py` and `g0.rs` plant `"poison"` alone in
generic code, which fails, and a message that holds it, which passes. Generic
code that one day needs the bare spelling takes it from the dialect through a
class, or ADR-2026-11-03-0600 moves the line (ADR-2026-11-03-0600). Rejected: a
list of exempt generic terms, which would let per-op code for the op `poison`
into generic code unseen; renaming the op, which the human named `poison` on
2026-11-03 (#122).

## Program structure

fir is a CFG: a function body is a graph of blocks, linked by branches. It is
not a sea of nodes and not an RVSDG. Effectful ops are ordered by their
position in a block. An earlier op's effects happen before a later op's. A pass
that moves an effectful op must keep every effect order the source fixes
(ADR-2026-10-29-2005). This is E0. Rejected: a sea of nodes or an RVSDG, where
only dependence edges order ops, so printing, interpreting or lowering a
function needs a scheduling step to recover an order.

This order binds the core dialect. Extension dialects may define other region
kinds, such as unordered dataflow regions. The format admits them, and M1 builds
none (ADR-2026-11-09-1543). Explicit memory tokens may come later as a stricter
mode, without replacing the CFG (ADR-2026-10-29-2005).

fir is in SSA form, with block arguments and no phis. A block declares typed
arguments. A branch passes one value per argument of its target. Both `br` and
`cond_br` pass block arguments. The verifier checks the count and the types at
every branch (ADR-2026-10-29-2010). This is H1. Rejected: phi nodes, as in
LLVM. Block arguments make a branch a jump that carries values, like a call, and
need no rule that ties phis to predecessors.

A function is a region isolated from above. Nothing in one function references
a value of another function. Functions reach each other only by symbol. In
Rust, ownership keeps functions apart, and the verifier checks isolation
itself (ADR-2026-10-29-2011). This is H2. Rejected: values shared between
functions, since then no function could be checked, changed or compiled
without the others.

An op refers to a function or other global by symbol only, as in `call @f`.
Constants are ordinary ops inside the function, not module-level values. The
IR keeps no module-wide use-lists: finding every user of a symbol takes a scan
of the module, or an index that a pass builds for itself. The verifier resolves
every symbol reference (ADR-2026-10-29-2012). This is H3. Rejected: LLVM's
globals and constants as values with use-lists shared by every function, so
that changing one function touches state that others share.

Symbol tables must be able to nest. M0 does not use nested modules, but its
data structures must not rule them out (ADR-2026-10-29-2016). M1 designs global
items and function addresses (ADR-2026-11-09-1546, ADR-2026-11-09-1548) and
`module` items (ADR-2026-11-09-1543).

fir has no nesting limit. Every text the grammar accepts is read at any depth,
and the IR holds any depth. Every tool, in Rust and in Lean, handles any depth
on a small stack. Memory bounds how deep a text
can go, not the stack. No tool relies on a large reserved stack. The tests of
each tool nest texts deeper than a recursive walk on a small stack could reach
(ADR-2026-10-30-1549). The human ruled this on 2026-10-30 (#36): "There's no
point in introducing a random nesting limit." Rejected: a nesting limit in the
spec, which changes the text format, and a limit in each tool reported as a
resource error, which would make `funk` and `fir-ref` disagree on deep texts.
rust-ir-and-tools.md says how `funk-ir` keeps its walks off the stack.

## Integers and numbers

fir integer types are bitvectors `iN`. Signedness lives on ops, never on types.
Every op whose meaning depends on sign comes in a signed and an unsigned form,
such as `sdiv` and `udiv`. Pointer types are separate: `ptr<N>` points into the
memory `N`, and the core `ptr` is `ptr<0>`. A value of a pointer type is poison
or a pointer (ADR-2026-11-09-1542). No op makes one yet, and `ptradd` moves one
(ADR-2026-11-13-0251; semantics-m1-design.md says how). These types
belong to the core dialect, not to a closed type system (ADR-2026-10-29-2007).
This is S2. Rejected: signed and unsigned integer types. Signedness is a
property of an operation, and one bit pattern is read both ways.

An integer type `iN` has `1 <= N <= 16,777,215`, which is `2^24 - 1`:
`maxWidth` in `lean/Fir/Core/Types.lean` and `MAX_WIDTH` in
`crates/funk-ir/src/dialects/core/types.rs`. The IR
and the Lean interpreter accept every width in that range. A wider type does
not decode, in Lean and in Rust alike. A frontend that needs a wider integer
has to split it (ADR-2026-10-29-2007). A float type `float<e,m>` is no wider
than that in all, and semantics-floats.md says which formats the core takes
(ADR-2026-11-09-1549).

Every other number that gives the text its structure is below `2^32`: a
location reference, a line and a column. An integer attribute has no bound of
its own. The dialect that reads it bounds it, as a core constant must fit its
type. A number out of its range is a parse error, located at the number
(ADR-2026-10-29-2007). `tests/fir/canonical/widths.fir` holds `i16777215`, and
`tests/fir/reject/tokens.toml` rejects `i16777216` and a location reference,
a line and a column of `2^32`. These are MLIR's limits, N3, which the human
ruled on 2026-10-30 (part 3 of the rulings comment on #5). Rejected: S2's first
wording, any width `N >= 1`, since every tool holds a width, a line or a
location reference in an integer of fixed width.

The M0 backend supports `i1`, `i8`, `i16`, `i32`, `i64` and `i128`. `i128`
lowers to register pairs, with division through a runtime helper. The backend
rejects any other width with a clear diagnostic. Odd widths, such as `i7` and
`i33`, are tested on the interpreter only (ADR-2026-10-29-2007).
