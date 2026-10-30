# `fir-ref run` follows the path that `--choices` names by default, and lists every outcome with `--exhaustive`

Status: accepted

## Context

ADR-2026-10-30-1856 defines `fir-ref run` for a run with one path, and
leaves to [#14](https://github.com/pmatos/funk/issues/14) how it reports a
set. ADR-2026-10-29-2017 gives `fir-ref` an exhaustive mode, which prints
every outcome within a budget on the choice bits, and a scripted mode,
which takes a choice sequence and prints one outcome. #14 asks for:

- JSON that documents the outcome set, the result when the budget is
  exceeded, and whether any choice was used;
- a documented input format for scripted mode, each choice spelled as a
  constant;
- a sequence that does not fit the run, too short, too long or with a
  choice that is not a value of its type, reported as an error of its
  own, never as an outcome, so that a stale witness fails loudly (comment
  6507459651 on #14).

The harness (ADR-2026-10-30-2049, ADR-2026-10-30-2135) and
`scripts/check-fir-ref.sh` read `fir-ref run`'s JSON by its `kind`, its
values and its exit status. Every corpus run makes no choice.

## Decision

- **Command.** `fir-ref run [--fuel N] [--choices C,C,...]
  [--exhaustive [--choice-bits B]] FILE @FUNC [ARG...]`. Options come
  anywhere before `--`, and each takes the next argument as its value.
  `--choices` with `--exhaustive`, and `--choice-bits` without it, are
  usage errors.
- **Scripted mode is the default.** It follows the one path that the
  choice sequence names. `--choices` gives the sequence: the choices in
  the order the run makes them, separated by commas, with no spaces. Each
  is spelled as a constant of the type of its choice, as arguments are:
  `true` or `false` at `i1`, signed decimal at every other width. `freeze`
  at `iN` makes a choice of type `iN`. The empty text is the empty
  sequence, which is the default, so a run that makes no choice runs as
  it did before #14.
- **Scripted result.** ADR-2026-10-30-1856's object for the path's one
  outcome, with one more field, `choices`: the number of choices the path
  made, `0` when it made none. For example,
  `{"kind":"return","values":["0"],"choices":1}`. The exit status is
  ADR-2026-10-30-1856's.
- **A sequence that does not fit.** It is an argument error: one line on
  standard error, `fir-ref: @f: the choices do not fit the run: REASON`,
  nothing on standard output, and exit status 2. The reason says which:
  the run makes a choice after the sequence ends, the sequence has values
  left when the path ends, or a value is not a constant of its choice's
  type. A path that reaches an op without rules reports that error
  instead (ADR-2026-10-30-1855).
- **Exhaustive mode.** `--exhaustive` tries every choice sequence. A
  choice's values are tried from zero up, read as unsigned. The budget,
  `--choice-bits B` with B ASCII decimal digits, bounds the bits that one
  path chooses in all; it is 16 by default, so at most 65,536 paths.
- **Exhaustive result.**
  `{"kind":"outcomes","choices":N,"outcomes":[O,...]}`. Each `O` is
  ADR-2026-10-30-1856's object for one way a path ends, without
  `choices`: every outcome of the run, each once, in the order the paths
  first reach it, and a stuck path as `{"kind":"stuck",...}`. `N` is the
  most choices that one path made, so `0` means that the run made none.
  The exit status is 1 when a path is stuck, and 0 otherwise.
- **Budget exceeded.** When a path would choose more than B bits,
  exhaustive mode prints `{"kind":"choice-budget-exceeded","budget":B}`
  and exits with 0: it is a result, which a tool tells apart from an
  error by its `kind`. A path that reaches an op without rules is
  ADR-2026-10-30-1855's error, with exit status 2. The budget is checked
  first: a run that exceeds it reports that, even when a path reaches an
  op without rules.
- **Proofs.** Within its budget, exhaustive mode lists exactly the run's
  outcomes, and scripted mode, on a sequence that fits, gives one of them
  (`Core.exhaustive_outcomes`, `Core.scripted_outcomes`,
  ADR-2026-10-30-2217). Exhaustive mode is within its budget exactly when
  no path chooses more than B bits (`ChoiceTree.explore_isSome_iff`).

## Alternatives

- **Exhaustive mode by default.** It would change the output of every
  existing run, and every reader of it, in one step. A scripted default
  keeps a run that makes no choice as it was, and a run that chooses
  fails loudly until a mode is given.
- **A JSON `kind` for a sequence that does not fit.** The choices are
  arguments, and an argument that is not a value of its type is already
  an error on standard error with status 2. A tool error never passes.
- **One `--choice C` option per choice.** The empty sequence would then
  need an option of its own.
- **A larger default budget.** 16 bits, 65,536 paths, keeps a run within
  seconds; `--choice-bits` raises it.

## Consequences

- The harness reads `choices` to know that a run made none. Its set rule,
  declared results with witnesses, and seeded sampling, which call the
  modes, land in #14's harness stage.
- Every scripted result has a new field, so readers that compare whole
  objects, such as `scripts/check-fir-ref.sh`, expect it.
- A witness is a `--choices` text, so a test can store it as a list of
  strings and join it with commas.
