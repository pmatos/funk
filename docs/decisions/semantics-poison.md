# Current decisions: semantics, poison and UB

This page continues semantics.md. It says what holds today about poison,
immediate UB and `freeze`. It is the record: when this page and an ADR disagree,
the page wins, and the ADR is fixed or deleted (ADR-2026-11-09-1610).

## Poison, UB and freeze

fir has one deferred-UB value, poison, plus the `freeze` op. There is no
`undef`. Poison stays distinct from immediate UB. The flags `nsw`, `nuw` and
`exact` turn their failure into poison. A shift amount `>= N` gives poison
(ADR-2026-10-29-2006).

Branching on poison is immediate UB. It does not go to either successor. A
compiler could otherwise not use what a branch tests (ADR-2026-10-30-0818).
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

Poison follows these rules (ADR-2026-10-30-0818):

- A poison operand gives a poison result, unless an op says otherwise.
- `select` with a poison condition gives poison.
- A poison divisor is immediate UB, because it might be zero.
- `sdiv` and `srem` by `-1` are immediate UB when the dividend is poison,
  because it might be the signed minimum.
- Every other poison dividend gives poison.
- A poison shift amount gives poison.
- `zext` and `sext` strictly widen, and `trunc` strictly narrows. These are
  validation rules.

Both division rules come from one principle. A poison operand is immediate UB
wherever some value it could take would be UB. So the x86-64 backend can emit a
bare `idiv` (ADR-2026-10-30-0818).

Propagation is checked, not only stated. Every op of every dialect declares a
poison class through `DialectEffects`: `propagates` or `exception`
(ADR-2026-10-30-0818). In the core dialect, 24 ops propagate and seven are
exceptions (ADR-2026-11-03-1615). The float constant, `fcmp` and the three ops
of float arithmetic are among the 24 (ADR-2026-11-11-1139,
ADR-2026-11-11-1800). `select`, `freeze` and `cond_br` are
exceptions with their own rules. `br`, `ret` and `call` are exceptions that pass
values on as they are (ADR-2026-10-30-0818). `unreachable` is an exception that
is always UB, which the obligations below allow (ADR-2026-11-09-1548). The core dialect lists each op by
its constructor in `Core.Op.poisonClass`, with no case for the rest. So a new
core op does not build until it declares its class (ADR-2026-11-03-0600).

`LawfulDialectPoison` holds the obligations (ADR-2026-10-30-0818):

- `PropagatesPoison`, for a propagating op. From operands of which one is
  poison, every result it returns is poison. It is UB on such operands only by
  its own rules, under the principle above.
- A propagating op also returns a result on some operand vector with no poison.
  Exceptions are exempt, so an exception that is always UB stays allowed.
- Total: an op has an outcome on every operand vector, and a terminator's exit
  has one too.
- Monotone: refining an op's operands refines what it does. A poison value is
  refined by every value of its type.

Total and monotone cover only the ops that the interpreter runs by their own
rule: terminators and ops with no callee (ADR-2026-11-02-1514). An extension
dialect declares a class for each of its ops and proves the obligations
(ADR-2026-10-30-0818). `LawfulDialectPoison CoreDialect` holds with no `sorry`
(ADR-2026-11-03-1615).

The core dialect writes poison with `poison`, its 25th op. It is written
`%p: iN = poison @L`, with no attributes and no operands. It gives the poison
of `iN` on every run. It is never UB and makes no choice. Its class is
`propagates`, as for `const`. Its result type must be valid, as for `const`.
Native code may lower it to any value (ADR-2026-11-03-1615).

The spec states two forbidden rewrites, and passes must not perform them. A
`select` becomes a branch only with its condition frozen. `select %c, %x, false`
is not `and %c, %x` when `%x` may be poison (ADR-2026-10-30-0818).

Every field of `LawfulDialectPoison` covers only op instances that meet
`TypesValid`. That means each operand type and each result type is valid for
its dialect. Every op of a valid function meets it. A dialect proves its
obligations only for the instances that its validation accepts. Division at
`i0` keeps its rule (ADR-2026-11-02-1515).

Ticket #16 tests the rewrite of `select` into `and`, and #19 tests the rewrite
into `cond_br`
([testing-and-harness-corpus.md](testing-and-harness-corpus.md#the-tests-of-the-select-rewrites)).
