# A callee runs with the fuel its caller has left, and gives back the rest

Status: accepted

## Context

[#20](https://github.com/pmatos/funk/issues/20) says that all calls share
the fuel budget of a run, so that runaway recursion reports fuel
exhaustion. [#10](https://github.com/pmatos/funk/issues/10) asks for an
interpreter to which #20 adds its call effect without restructuring it.
The human ruled on [#70](https://github.com/pmatos/funk/issues/70)
(2026-11-02) that #10 designs this before it proves `FuelMonotone`,
`Progress` and `NeverStuck`.

Until now the budget was the structural `Nat` argument of `Func.runOps`,
lowered by one per op. An op's `denote` and `exit` see only the op and its
operands: not the module, which a call needs to find its callee, and not
the budget, which the callee must share. The set monad has no module.

Fuel is a device of the Lean definitions. It must not change what a
program means, nor any result of `fir-ref`.

## Decision

- **The run provides the call effect.** A dialect names the function that
  an op calls through `DialectCall` (`callee?`, in
  [`lean/Fir/Execution/Effects.lean`](../../lean/Fir/Execution/Effects.lean)).
  The interpreter runs that op, not its `denote`: it finds the callee in
  the module by symbol, passes the op's operands as its arguments, and
  binds the values that the callee returns to the op's results. No core
  op has a callee yet; #20 names the callee of `call`.
- **A run belongs to a module.** `Func.runOps M n f env os` and
  `Func.run M f args fuel` take the module whose functions calls run.
- **Budget in, rest out.** Fuel stays the interpreter's argument, not
  state in the monad. Every op takes one step, a call included.
  `Func.runOps` returns the steps it leaves with the values it returns.
  A callee gets the steps that its caller has left after the call's step,
  and the caller goes on with the steps that the callee gives back. A
  callee that runs out of fuel ends the run so; its UB and stuck paths are
  its caller's.
- **Well-founded on the budget.** The caller goes on with the callee's
  rest, which is not a subterm of the budget, so the recursion is
  well-founded on the budget (`termination_by`), not structural. A run
  leaves at most its budget (`Func.runOps_left_le`); the definition goes
  on with `min k n`, which is `k`, so that Lean sees the budget shrink.
  Nothing is `partial`.

## Alternatives

- **Fuel as the structural argument, passed to a call hook**, the
  suggestion on #70. Kept in substance: the callee is handed the budget
  and gives back the rest. Changed in one point: the recursion cannot
  stay structural, for the reason above. `FuelMonotone` is still proved by
  induction on the budget.
- **Fuel in a state monad.** A second counter beside the interpreter's,
  or termination that rests on a counter Lean cannot see; `FuelMonotone`
  would be about the wrong counter.
- **A call effect as a class on the monad**, like `MonadChoice`. The set
  monad has no module, and `denote` cannot see the budget.
- **An op step that takes the budget and a runner of functions.** Each
  dialect would count fuel itself, and fuel monotonicity would need a
  proof for each op.
- **A machine with a stack of frames.** Structural, but a callee's steps
  would no longer be a run of its function, so #20's proofs about callees
  (refined arguments, a refined callee) would need a lemma relating the
  two.

## Consequences

- #20 adds the callee of `call` to `DialectCall CoreDialect`, with its
  tests and proofs, and does not change the interpreter.
- No result of `fir-ref` changes: no core op calls a function yet, each op
  still takes one step, and a function's run returns what it returned.
- Fuel monotonicity holds for every function of every module, calls
  included, whatever its ops do (`Func.fuelMonotone`), since only the
  interpreter counts fuel.
- `Progress` and `NeverStuck` for runs with calls are #20's to prove.
