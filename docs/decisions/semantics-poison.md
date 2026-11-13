# Current decisions: semantics, poison and UB

This page continues semantics.md. It says what holds today about poison,
immediate UB and `freeze`. It is the record: when this page and an ADR disagree,
the page wins, and the ADR is fixed or deleted (ADR-2026-11-09-1610).
ADR-2026-10-29-2006 holds the direction decision.

## Poison, UB and freeze

fir has one deferred-UB value, poison, plus the `freeze` op. There is no
`undef`. Poison stays distinct from immediate UB. The flags `nsw`, `nuw` and
`exact` turn their failure into poison. A shift amount `>= N` gives poison
(ADR-2026-10-29-2006). The human chose this on 2026-10-29 (S1 on #5).
Rejected: `undef` beside poison, as LLVM has. Each use of one `undef` may see a
different value, so `add %x, %x` can be odd where `mul %x, 2` is even, and
common rewrites become unsound.

Branching on poison is immediate UB. It does not go to either successor. The
human confirmed this on 2026-10-30 (N1, part 3 of the rulings on #5). Rejected:
a branch on poison goes to either successor. A compiler could then no longer use
what a branch tests: after `%c = icmp eq %x, %y; cond_br %c, ...`, replacing
`%y` with `%x` in the first successor is sound only if a branch on poison is UB.

Reaching the terminator `unreachable` is immediate UB too. It has no operands
and no successors, and its effects are may-UB and control
(ADR-2026-11-09-1548, ADR-2026-11-09-1541). The naive backend lowers it to
`ud2`, and a test whose run reaches it is interpreter-only.
Division by zero is immediate UB, and so is `INT_MIN / -1`
(ADR-2026-10-29-2006).

`freeze` of poison yields an arbitrary but fixed value. Every use of the result
sees the same value, and native code must give every use the same bits
(ADR-2026-10-29-2006). The interpreter's monad has a `choose w` effect, which
`freeze` of poison calls. With the set instance of the monad, the interpreter
defines the semantics: the set of behaviours over all choices
(ADR-2026-10-29-2017).

The spec explains poison, immediate UB, `freeze` and the asymmetry between
`select` and `cond_br` in plain words, in `lean/Fir/Execution/PoisonUB.lean`.

## How poison propagates

The human ruled on 2026-10-30 to adopt LLVM's rules, with two improvements
(parts 3 and 4 of the rulings on #5). Poison follows these rules
(ADR-2026-10-29-2006):

- A poison operand gives a poison result, unless an op says otherwise.
- `select` with a poison condition gives poison.
- A poison divisor is immediate UB, because it might be zero.
- `sdiv` and `srem` by `-1` are immediate UB when the dividend is poison,
  because it might be the signed minimum.
- Every other poison dividend gives poison.
- A poison shift amount gives poison.
- `zext` and `sext` strictly widen, and `trunc` strictly narrows. `fpext`
  goes to a float format that holds every value of the source, and `fptrunc`
  to one that cannot ([semantics-floats-conversions.md](semantics-floats-conversions.md#the-conversions)).
  These are validation rules.

Both division rules come from one principle of LLVM's reference. A poison
operand is immediate UB wherever some value it could take would be UB (LangRef,
"Poison Values"; Alive2's `div_ub` agrees). So the x86-64 backend can emit a
bare `idiv`. Rejected by the human (part 4): a poison dividend by `-1` gives
poison. `sdiv` would not be monotone, since refining that poison to the signed
minimum turns a result into UB, and a backend would need a guard before every
`idiv`.

The spec states two forbidden rewrites, and passes must not perform them. A
`select` becomes a branch only with its condition frozen. `select %c, %x, false`
is not `and %c, %x` when `%x` may be poison (ADR-2026-10-29-2006). Ticket #16
tests the rewrite of `select` into `and`, and #19 tests the rewrite into
`cond_br`
([testing-and-harness-corpus.md](testing-and-harness-corpus.md#the-tests-of-the-select-rewrites)).

## Poison classes

Propagation is checked, not only stated. Every op of every dialect declares a
poison class through `DialectEffects`: `propagates` or `exception`
(ADR-2026-10-29-2006). Rejected: propagation in prose only, as LLVM's reference
states it. An op whose rules forget to propagate poison would go unnoticed.

In the core dialect, 32 ops propagate and seven are exceptions. The 32 are
`const`, the float constant and `poison`, which have no operands, `add`, `sub`
and `mul`, the four divisions, the bitwise ops and shifts, `icmp`, the width
changes, `fcmp`, the three ops of float arithmetic, the two bit casts, the
two conversions from integers, `sitofp` and `uitofp`, the two conversions
between formats, `fpext` and `fptrunc`, and the two conversions to integers,
`fptosi` and `fptoui` (ADR-2026-11-09-1549). `select`, `freeze` and `cond_br` are
exceptions with their own rules. `br`, `ret` and `call` are exceptions that pass
values on as they are, to block arguments, the caller or the callee.
`unreachable` is an exception that is always UB, which the obligations below
allow (ADR-2026-11-09-1548). The core dialect lists each op by its constructor
in `Core.Op.poisonClass`, with no case for the rest. So a new core op does not
build until it declares its class (ADR-2026-11-03-0600). An extension dialect
declares a class for each of its ops and proves the obligations
(ADR-2026-10-29-2006).

## The obligations

`LawfulDialectPoison` holds the obligations (ADR-2026-10-29-2006):

- `PropagatesPoison`, for a propagating op. From operands of which one is
  poison, every result it returns is poison. It is UB on such operands only by
  its own rules: only if it is UB on some operands that put a defined value in
  place of each poison and agree with them elsewhere. This is the principle
  above, in Lean.
- A propagating op also returns a result on some operand vector with no poison.
  Without this, an op that is always UB would meet both poison clauses, since
  UB would be its own rule. Exceptions are exempt, so an exception that is
  always UB stays allowed.
- Total: an op has an outcome on every operand vector, and a terminator's exit
  has one too.
- Monotone: refining an op's operands refines what it does. A poison value is
  refined by every value of its type.

Total and monotone look only at what runs: the semantics of an op that is not a
terminator, and the exit of a terminator. Rejected: an obligation on returned
results only. An `add` that turns a poison operand into UB, or into no outcome,
would meet it, and that would undo the deferral that poison exists for.

The obligations reject a wrong op, and the theorems of
`lean/Fir/Core/Unlawful.lean` check it: an op with no outcome, an `add` that is
UB on a poison operand, the rejected `sdiv` rule, and a semantics in which every
op is always UB. The obligations do not fix what an op computes: each family's
semantics does. `LawfulDialectPoison CoreDialect` holds with no `sorry` and only
the standard axioms (`Core.lawfulDialectPoison`).

### Ops with a callee

Total and monotone cover only the ops that the interpreter runs by their own
rule: terminators and ops with no callee
(`isTerminator op = true ∨ callee? op = none`). A call's meaning is its callee's run, so `call` has no op-level rule
(ADR-2026-10-29-2006). The human ruled this on 2026-11-02, on #20. The
hypotheses that ask every op to be total or monotone carry the same guard: those
of the progress proof with calls (`Module.calls_hasPath`,
`Func.progress_of_inModule`) and those of the refinement engine
(`Func.runOps_allowed`, `Func.runs_isRefinedBy_of_calls` and the theorems under
them). `Core.Op.total_all` and `Core.Op.monotone_all` hold for every core op
that meets the guard: every core op but `call`. Rejected: a stand-in rule for
`call`, immediate UB in the set monad, so that it would meet the op-level
obligations. It claimed a meaning that a call does not have, and as a source it
was refined by every computation, so a statement proved op by op would hold for
every rewrite of a call. semantics-interpreter.md says how `call`'s `denote`
reads now.

### Valid op instances

Every field of `LawfulDialectPoison` covers only op instances that meet
`TypesValid`: each operand type and each result type is valid for its dialect
(`validTy`, in `lean/Fir/Validation/Rules.lean`), and `poison_isRefinedBy`
speaks of valid types. It reads no context, so it is
a property of the op instance alone; the core dialect instantiates it with
`Core.Ty.Valid`. Every op of a valid function meets it
(`Func.Valid.typesValid`), so no valid program changes meaning. A dialect proves
its obligations only for the instances that its validation accepts
(ADR-2026-10-29-2006). The human ruled this on 2026-11-02, on #69, and the
orchestrator took the sub-choice that #69 recommended: the whole class, not
only `returnsOnDefined`.

Division at `i0` keeps its rule, and is the reason for the narrowing: at `i0`
every divisor is zero, so no division returns a result on defined operands
(`Core.div_zero_width`). Rejected: change division at width zero, which changes
the rule of an instance that no valid module holds only to make the class
provable. Rejected too: ask `validOp` as well, which needs a context, the symbol
table and the function's result types, that an op instance alone does not have;
validation checks its rules in each function. The refinement engine asks
monotonicity only of the ops a run can reach, so the class gives refinement for
valid modules, and the core dialect meets it at every width, `i0` included, with
`Core.Op.monotone_all`
([semantics-refinement.md](semantics-refinement.md#the-ops-a-run-reaches)).

## The poison op

The core dialect writes poison with the op `poison`
(ADR-2026-10-29-2006). The human ruled on 2026-11-03, on #122, that the core
gains it in M0. Rejected by the human: a reserved operand `%poison`, which
changes the generic grammar.

- It is written `%p: iN = poison @L`, with no attributes and no operands.
  `Op.decode` reads it only so, with one `iN` result. Its result type must be
  valid, as for `const`.
- It gives the poison of `iN` on every run. It is never UB and makes no
  choice. Its rule and its obligations sit beside `const`'s, in
  `lean/Fir/Core/Arith.lean` and its laws.
- Its class is `propagates`, as for `const`. No operand vector of `poison`
  holds a poison, so both poison clauses hold, and on the empty vector it
  returns its one result, which meets the obligation of a result on operands
  with no poison. Rejected: class `exception`, which states a rule for poison
  operands, and `poison` has none; `propagates` asks more of it and holds.
- `funk-ir` registers it beside `const` (`dialects/core/constant.rs`), and
  both printers write the same bytes for it.
- Native code may lower it to any value
  ([x86-64-backend.md](x86-64-backend.md#poison)).
