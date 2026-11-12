# `fir-ref run` keeps recent values in a list and moves older ones into a map when lookups have paid for it

Status: accepted
Tier: implementation; area: fir-ref

## Context

The spec's environment, `Env` in
[`lean/Fir/Execution/Interpreter.lean`](../../lean/Fir/Execution/Interpreter.lean),
is a list. Every op and every jump puts values in front of it, and
`Env.value` looks a name up from the front. So an operand costs time for
each value defined after it, and in a loop the list grows with the steps
run. The machine that `fir-ref run` walks (ADR-2026-11-04-2132) kept that
list, so a block of `add` ops that each read the parameter took 79.7 s at
100,000 ops, and a loop that reads values from before it 10.1 s at 100,000
steps ([#47](https://github.com/pmatos/funk/issues/47), stage 6).

`fir-ref run` must give the spec's answer on every input, valid or not:
the latest of two definitions of a name, the first of two names that one
bind defines, a value of a block that does not dominate the read, block
arguments bound again on each jump, and a callee that sees none of its
caller's names. The human held stage 3 of #47 rather than accept a CPU
cost, so this stage set out to make no input slower than before. On
2026-11-05 the human ruled that performance on the Lean side is not a
concern, up to ten times slower than the Rust side but never hours on a
simple example, and that this stage merges with the slower inputs it
leaves, without a search for a better design (#47,
[comment](https://github.com/pmatos/funk/issues/47#issuecomment-6652389282);
PR #140,
[comment](https://github.com/pmatos/funk/pull/140#issuecomment-6652389604)).

A map that binds each name once costs about 0.65 to 0.85 µs to insert into
at a million names (`Std.TreeMap` and `Std.HashMap`, measured), and the
whole step of a run of a million `const` ops costs about 0.85 µs today.
Putting every value into a map would double that run's steps.

## Decision

- **The machine keeps its values in `FirRef.Bindings`**
  ([`lean/FirRef/Bindings.lean`](../../lean/FirRef/Bindings.lean)):
  `young`, a list of the latest values, the latest first, as in the spec,
  in front of `old`, a `Std.TreeMap` that binds each name once. A bind puts
  values in front of `young`, as the spec does. A lookup searches `young`,
  then `old`.
- **Lookups pay rent, and `young` moves when they have paid for it.** A
  lookup that passes at most `deep` = 128 entries of `young` costs
  nothing; one that passes more adds every entry it passed to a debt.
  When the debt exceeds `rent` = 32 times the length of `young`, `young`
  moves into `old` (`settle`), the latest value of each name winning.
  `Bindings.args` looks each operand of an op up once and pays for all of
  them at once. `rent` and `deep` set how `fir-ref` spends its time; they
  are not rules of fir or thresholds of a check, and any values give the
  same results.
- **Each operation is proved to fit the spec's.** `Bindings.args`, `bind`,
  `bindResults`, `jump` and `enter` stand for `Env.operands`, `Env.bind`,
  `Func.jump` and `Func.enter`, with the same errors and messages, and
  give bindings that give every name what the spec's new environment gives
  it (`Bindings.Fits`,
  [`lean/FirRef/BindingsSteps.lean`](../../lean/FirRef/BindingsSteps.lean)).
- **A run depends on its environment only through lookups.**
  `Machine.runOps_congr`
  ([`lean/FirRef/Steps.lean`](../../lean/FirRef/Steps.lean)) proves that
  two environments that give every name the same value give the same run.
  A state of the machine stands for the spec's computation in the
  environment of its bindings, `Bindings.toEnv`, and
  `Machine.advance_tree` holds as before. The `@[csimp]` theorems of
  `FirRef.Run` keep their statements; their axioms are now Lean's three
  standard ones, since `Std.TreeMap`'s lemmas use `Classical.choice`
  (ADR-2026-10-30-1452 allows all three).

## Alternatives

- **One binding per name in a map, on every bind.** Simplest to prove,
  but each bind costs a map insert: about 0.65 to 0.85 µs at a million
  names, a run of a million `const` ops slower by about that much per op.
- **A `Std.HashMap` for `old`.** In exhaustive mode the paths after a
  choice share their bindings, and a shared hash map copies its whole
  bucket array on its first insert. A persistent tree copies one path.
- **Debt from the ninth entry (`free` = 8), as first built.** Calls whose
  ops read values 9 to 64 back ran 12% to 45% slower than on the spec's
  list: their lookups moved `young` into `old` again and again, and a
  search of the map costs more than a walk of a few dozen entries.
- **A larger `rent`.** It moves the slower inputs to more reads without
  making them faster, and slows the shapes this stage fixes: with the
  first version, at 1,024, a loop of 1,000,000 steps took 4.9 times as
  long as at 32.
- **One move shared by the paths after a choice**, through a map that the
  bindings at the choice compute when a path first needs it. Not built:
  the human ruled that the slower inputs below are accepted as they are.
- **Change the spec's `Env`.** The spec keeps its readable definitions,
  which its proofs are about (ADR-2026-10-30-1450).

## Consequences

- The lookups of a path take time near linear in the values it binds and
  the lookups it makes: lookups pass each entry of `young` about `rent`
  times on average before it moves, and it moves once, into a map of at
  most one value per name, whose inserts and lookups take time logarithmic
  in its size. A block of 100,000 `add` ops that read the parameter runs
  in under a second, and a loop of 1,000,000 steps that reads values from
  before it in about 1.3 s; their instructions grow tenfold for each
  tenfold. Runs whose ops read values at most `deep` back, calls among
  them, cost what they cost before, or less.
- Some inputs are slower than on the spec's list, as the human accepted. A
  run that reads one of its oldest values just often enough to move
  `young` into `old`, and then stops, pays for a move that it never uses;
  every index built on demand has such inputs. Measured against the
  spec's list (CPU time):
  - one function of 100,000 to 1,000,000 `const` ops, then 33 to 40
    reads of the first: 5% to 15% slower; from about 48 reads the move
    pays for itself;
  - a callee that binds more than `deep` values, reads its first 33 to
    64 times and returns, called again and again: up to 1.6 times as long
    at 1,000 and at 10,000 values;
  - exhaustive mode: the paths after a choice share `young`, and each path
    that moves it pays for its own move. 10,000 to 100,000 `const` ops,
    eight one-bit choices (256 paths) and 33 to 64 reads of the first on
    each path take up to 2.6 times as long;
  - in exhaustive mode, each path's first bind copies its bindings'
    record, which the spec's list does not: runs of thousands of short
    paths take up to 3% more cycles. A long search counts what it passes,
    four entries at a time, so it runs about 2% more instructions per
    entry than `List.lookup`; its time stayed between 5% faster and 4%
    slower than the spec's.
- Each environment is one more object of five words: a recursion one
  million calls deep takes 194 MB, not 156 MB.
- A change to `Env.operands`, `Env.bind`, `Func.jump` or `Func.enter`
  breaks the proofs of `FirRef.BindingsSteps` until `Bindings` follows.
  ADR-2026-11-04-2132's machine now calls these operations on bindings,
  not the spec's on lists.
