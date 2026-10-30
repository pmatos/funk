# A core op without execution rules has no outcome, and `fir-ref run` reports it, until its family lands

Status: accepted

## Context

The spec's `DialectDenote CoreDialect SetM` is one instance over all 24
core ops, and Lean needs a value for each of them.
[#10](https://github.com/pmatos/funk/issues/10) gives rules to its tracer
subset only: `const`, `add` without flags and `ret`. Tickets #14 to #20 give
the other ops theirs, and #14 gives `add` its flags. #10 asks for a
decision, recorded here, on what the instance and `fir-ref run` do with the
other ops meanwhile, with no stand-in semantics that looks final (no
stubs, as `AGENTS.md` says).

Facts about the obligations of ADR-2026-10-30-0818:

- An op with no outcome, the empty set, fails totality (`OpTotal`). It
  meets monotonicity and the poison clauses, since they say only what an
  op may do. `Core.Unlawful.noOutcome` shows the rejection.
- An op that may do anything, every result and every UB, is total and
  monotone. For an exception, such as `br`, `cond_br`, `select`, `freeze`
  or `call`, those are all its obligations, so it would pass for lawful.
- An op that is always UB meets the poison clauses
  (`Core.Unlawful.alwaysUB_propagatesPoison`), and gives these ops a
  meaning they do not have.
- Stuck is the interpreter's, for a case that validation rules out. A
  valid function that uses `sub` is valid, and an op's `denote` in the set
  monad cannot be stuck.

## Decision

- **Rules or none.** `Core.Op.denote?` and `Core.Op.exit?` give each core
  op its family's rule, written once for any monad, or `none` while its
  family has not landed (`lean/Fir/Core/Semantics.lean`).
- **No outcome in the spec.** In `DialectDenote CoreDialect SetM`, an op
  without rules has no outcome: its `denote` or its `exit` is the empty
  set on every operand vector. The interpreter does not change for it: a
  run that reaches the op has no way to end on that path.
- **An error in `fir-ref run`.** `fir-ref` runs the same rules. When a run
  reaches an op without rules, it prints no outcome: one line on standard
  error, `fir-ref: @f: OP has no execution rules yet`, with the op as text
  writes its name and attributes (`sub`, `add nsw`), nothing on standard
  output, and exit status 2. It never reports such a run as stuck or as UB.
- **Each family replaces `none`.** Each ticket from #14 to #20 adds its
  ops' rules to `Op.denote?` and `Op.exit?`, and proves their obligations
  in its own files.

## Alternatives

- **Every outcome.** It looks lawful for the exceptions, as above, and
  `fir-ref` cannot print it.
- **Always UB.** Wrong for every one of these ops, and `fir-ref` would
  report UB, which #13's harness reads as an invalid test.
- **Stuck.** Stuck means invalid, and these modules are valid.
- **No instance until #20.** The obligations of #10's ops, and the
  interpreter's proofs, need an instance now.

## Consequences

- `LawfulDialectPoison CoreDialect` cannot be proved while an op lacks its
  rules, since totality fails for it. A missing rule cannot be mistaken
  for a final one by any theorem.
- `Progress` and `NeverStuck` hold for the tracer subset only, as
  `Fuel.lean` says, until #14 to #20 extend them.
- The behaviour of a function that reaches an op without rules is empty,
  and an empty behaviour refines every source. No refinement is stated
  about such functions before their ops have rules.
- #13 sees exit status 2, a tool error, for a test that runs an op before
  its family lands, never a wrong result.
