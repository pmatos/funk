# Current decisions: validation

This page states what holds today for validation in fir and in `fir-ref`. It is
the record: when this page and an ADR disagree, the page wins, and the ADR is
fixed or deleted (ADR-2026-11-09-1610).

## Rules of validity

Every block of a fir function is reachable from its entry. Validation rejects
a function with a block that its entry does not reach. The verifier names that
block in its reason. The rule is `reachable` in `Func.Valid`, in
`lean/Fir/Validation/Rules.lean`. The spec proves the rejection as
`deadBlock_rejected`, in `lean/Fir/Core/Rejects.lean`. The human ruled this
on 2026-10-30, as choice 20 of the rulings on #5 (ADR-2026-10-30-0817).

Dominance has its standard meaning. Block `a` dominates block `b` when every
path from the entry to `b` passes through `a`. It needs no case for
unreachable blocks. Definitions cannot form a cycle (ADR-2026-10-30-0817).

Producers delete unreachable blocks before validation. That covers frontends
and passes alike. A pass can leave a block unreachable, say by folding a
branch. It then removes the block before the IR is verified. Verifiers and
passes may assume that every block is reachable. They may also assume that a
definition comes before its uses on every path from the entry
(ADR-2026-10-30-0817).

Rejected: LLVM's rule, which accepts unreachable blocks as dominated by every
block. Dead code could then hold cyclic definitions, which every verifier and
pass would have to tolerate (ADR-2026-10-30-0817).

## Nested modules

A module holds a symbol table at each level of nesting: its own, and that
of each nested module, at any depth. Each table is a dialect set and a
list of items. Validation checks every table with one rule,
`SymbolTable.Valid`, in `lean/Fir/Validation/Rules.lean`: each symbol names
one item of the table, of any kind; each function is valid against the
table's own symbols; each item of a dialect's kind is valid
(`DialectItem.Valid`: a kind that a dialect registers, distinct parameter
names, valid types, attributes that can be written and the dialect's rule
for the kind, ADR-2026-11-10-2224); and the set names each dialect once, by
a word. `Module.Valid` asks a valid location table and a valid table at each
level. One location table serves every table (ADR-2026-11-10-1510).

So a function and a module never share a symbol of one table, while a
nested module may reuse a symbol of its parent's. A call names a function of
its own table: never one of a nested module, of its parent, or a module.
The rule of the dialect set, `Module.InDialectSet`, holds for each table
against its own set (ADR-2026-11-10-1510).

`Module.tables` lists the tables, the module's own first, each before the
tables nested in it. Both validators report in that order: the location
table's problems, each table's problems, then each table's dialect-set
problems. A problem in a nested module names its function as one at the top
level does; the report's schema has no field for the module
(ADR-2026-10-30-1741).

## The spec's check

The spec has an executable check, `Module.problems`, in
`lean/Fir/Validation/CheckModule.lean`. It takes two things from a dialect,
and nothing more (ADR-2026-11-09-2257):

- `[DecidableEq d.Ty]`, the standard class.
- An instance of `DecidableDialectValidation d`, from
  `lean/Fir/Validation/Check.lean`. Its fields decide the dialect's five
  rules: `validTy` for every type, `validOp` for every context and op,
  `validFunc` for every function, `validRegion` for every region of a kind it
  registers (ADR-2026-11-10-1941) and `validItem` for every item of a kind it
  registers (ADR-2026-11-10-2224).

A module's dialect set has a rule of its own, `Module.InDialectSet`, in
`lean/Fir/Validation/DialectSet.lean`, beside `Module.Valid`. It reads the
module's words through the dialect's text, so `Module.Valid` and the
theorems about it need no text. Its check is `Module.setProblems`, and
`fir-ref validate` and `funk verify` report `Module.problems`, then
`Module.setProblems` (ADR-2026-11-10-1306).

A dialect's rules in `DialectValidation` stay propositions. A dialect that
wants the check proves them decidable. The core dialect does so case by case
in `lean/Fir/Core/Check.lean`. A new dialect derives `DecidableEq` for its
types and decides its rules. It then gets the check, and so `fir-ref
validate` (ADR-2026-11-09-2257).

Rejected: Boolean rules in `DialectValidation`. Every dialect would write each
rule twice, as a `Bool` and as the proposition that proofs use
(ADR-2026-11-09-2257).

The check agrees with the rules in both directions. `Module.problems_eq_nil_iff`
proves that a module has no problems exactly when it is valid. That gives the
instance `Decidable m.Valid` (ADR-2026-11-09-2257).

A dialect gives no reason when its own rule fails. The check says that the op
breaks its dialect's own rule, and gives the op's index and block. Messages
about a type or a dialect rule print neither the type nor the op instance.
They name the value, the op's index and its block (ADR-2026-11-09-2257).

Rejected: a reason in the class, such as `whyNot`. It needs another field and
a law tying it to the rule, and tools compare verdicts, never messages
(ADR-2026-10-30-1032, ADR-2026-11-09-2257).

The spec's check walks nested blocks once. `Func.problems` calls
`Func.allBlocks` and passes the list to `Func.problemsIn`. `Func.problemsIn`
reads no other nested part of a function, so `fir-ref` can replace the one
walk (see [validation-fir-ref.md](validation-fir-ref.md)).

## A dialect's rule over a function

A dialect may add a rule over a whole function, for what no op can see alone,
such as a value that must be used exactly once. In Lean it is `validFunc`, and
`Func.Valid` requires it. In `funk-ir` a dialect registers a `FuncSpec`, and
`verify` runs every registered rule. The core dialect has no such rule
(ADR-2026-11-09-2257).

The Lean rule sees the function of the host dialect through a
`DialectView`, which maps each host op and type to the dialect's own or to
`none`. So a rule is written once and holds in any sum of dialects. It reads
only the module's symbol table, and it must assume nothing about the function,
because validation calls it on every function (ADR-2026-11-09-2257).

Rejected: `validFunc : ModuleContext d → Func d → Prop`, with each sum
supplying its own rule. A dialect's rule would not compose when the sum moved
into the spec (ADR-2026-11-09-2257).

A broken function rule is reported at the function's entry block, with the
location of its first op, by both validators. `tests/dialects/use-once.cases` holds the cases of a
use-once toy dialect, which the Lean and Rust tests both read
(ADR-2026-11-09-2257).

## A base op in a sum of dialects

In the spec's sum `base ⊞ e`, a base op is checked by the base's own rule.
It sees only the symbols whose types are all the base's. It sees the
function's result types only when they are all the base's. Otherwise no base
op is valid in that function, `add` included. The human ruled on 2026-11-10,
on #227, to keep this strict rule: it may be relaxed later, and the core's
control ops are not made generic now (ADR-2026-11-09-2353).

Rejected: dropping the result types that the base cannot write. A core `ret`
could then return too few values (ADR-2026-11-09-2353).

An extension lifted into a larger sum follows the same rule against what it
depends on. Its op sees only the symbols whose types are all its own or its
dependencies', and is valid only where the function's result types all are
(ADR-2026-11-10-1310).

## Region kinds

An op instance states the kinds of the regions its op owns, each a word of
a dialect, never the core's: a region of the core's kind inside an op would
be structured control flow, which M1 leaves out. A dialect registers kinds,
each with a rule over a region of the function, seen through a view as a
function rule is. The rule says how values are scoped in the region, which
ops end its blocks and where its successors go. An op is valid only when its
regions have the kinds its op instance states, each registered, and each
obeys its rule. The core registers no kind, and its own kind's rule is the
rule of a function's body (ADR-2026-11-10-1941).

An op inside a region obeys the general rules that hold whatever the kind:
its regions, types, number of successors, symbols, its dialect's own rule
and its location; a successor's label is a name and the values it passes
are defined in the function. The check walks the function's blocks at any
depth and each op's own regions, one level down, so it takes no stack per
level (ADR-2026-11-10-1941).

In a sum, a region of a kind that the base registers obeys the base's rule,
and any other kind `e`'s rule. A dialect writes its kinds under its name, so
each kind goes to the dialect that registers it. A lift registers `e`'s
kinds. In `funk-ir`, a dialect registers a `RegionKindSpec`, under its
prefix (ADR-2026-11-10-1941).

Rejected: the owning op's dialect judges its regions. A kind could not then be
shared between dialects (ADR-2026-11-10-1941).

`tests/dialects/region-kinds.cases` holds the cases of a toy kind whose ops
are unordered: one block, only the toy dialect's ops and no terminator, and
uses of the block's results in any order or of the function's parameters.
The Lean and Rust tests both read it, so the two validators agree on each
case and both print each case as itself (ADR-2026-11-10-1941).

## How `fir-ref` runs the check

`fir-ref` runs the spec's check at any depth through implementations proved
equal to the spec's parts. [validation-fir-ref.md](validation-fir-ref.md)
says how.
