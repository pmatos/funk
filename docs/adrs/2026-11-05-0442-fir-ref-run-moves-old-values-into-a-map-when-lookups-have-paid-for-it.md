# `fir-ref run` keeps recent values in a list and moves older ones into a map when lookups have paid for it

Status: accepted

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
caller's names. No input may get slower than before: the human held stage
3 of #47 rather than accept a CPU cost.

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
  lookup passes the first `free` = 8 entries of `young` for nothing. Past
  those, the entries it passes are a debt. When the debt exceeds `rent` =
  32 times the length of `young`, `young` moves into `old` (`settle`), the
  latest value of each name winning. `rent` and `free` set how `fir-ref`
  spends its time; they are not rules of fir or thresholds of a check, and
  any values give the same results.
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
  (ADR-2026-10-30-1838 allows all three).

## Alternatives

- **One binding per name in a map, on every bind.** Simplest to prove,
  but each bind costs a map insert: about 0.65 to 0.85 µs at a million
  names, a run of a million `const` ops slower by about that much per op.
- **A `Std.HashMap` for `old`.** In exhaustive mode the paths after a
  choice share their bindings, and a shared hash map copies its whole
  bucket array on its first insert. A persistent tree copies one path.
- **Move `young` into `old` on the first lookup that passes more than
  `free` entries.** One lookup of the first of a million values would then
  cost a million inserts instead of one search.
- **Change the spec's `Env`.** The spec keeps its readable definitions,
  which its proofs are about (ADR-2026-10-30-1450).

## Consequences

- The lookups of a path take time near linear in the values it binds and
  the lookups it makes: lookups pass each entry of `young` about `rent`
  times on average before it moves, and it moves once, into a map of at
  most one value per name, whose inserts and lookups take time logarithmic
  in its size. A block of 100,000 `add` ops that read the parameter runs in
  0.51 s, and a loop of 1,000,000 steps that reads values from before it
  in 0.48 s. Runs whose ops read recent values cost what they cost before,
  or less.
- One lookup can still search all of `young`, as on the spec's list,
  until lookups have paid for the move. In exhaustive mode the paths after
  a choice share `young`, and each path that moves it pays for its own
  move.
- Each environment is one more object of five words: a recursion one
  million calls deep takes 194 MB, not 156 MB.
- A change to `Env.operands`, `Env.bind`, `Func.jump` or `Func.enter`
  breaks the proofs of `FirRef.BindingsSteps` until `Bindings` follows.
  ADR-2026-11-04-2132's machine now calls these operations on bindings,
  not the spec's on lists.
