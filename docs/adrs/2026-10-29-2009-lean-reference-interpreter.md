# fir's semantics is a monadic definitional interpreter in Lean, with fuel, in its own calculus

Status: accepted
Tier: direction; area: semantics

## Decision

- **A fuelled interpreter.** The semantics of fir is a monadic definitional
  interpreter, written in Lean, not built on interaction trees. Fuel bounds
  every run, so it always terminates, and fuel exhaustion is an outcome of
  its own that stands for non-termination.
- **The only interpreter.** It is a test oracle for development and CI, run
  as `fir-ref`, and never ships inside a compiler. Lean holds the semantics,
  the interpreter and its own `.fir` parser and printer; Rust holds the
  whole toolchain. A Rust evaluator may come later only as a copy tested
  against Lean, never as the definition.
- **Its own calculus, in LeanMLIR's shape.** No dependency on LeanMLIR, but
  its typeclass shape (`TyDenote`, `DialectSignature`,
  `DialectDenote.denote`) wherever that is cheap. Terms are extrinsically
  typed, with names, locations and a CFG of blocks; terminators return an
  `Exit`; a dialect states the effects it needs as class constraints on the
  monad.
- **Calls share the fuel.** A dialect names an op's callee through
  `DialectCall`, fixed by its symbol or picked by the op's rule when it runs,
  and the interpreter runs the callee in the run's module. The call effect is
  the run's, not a class on the monad. Fuel is the interpreter's argument:
  every op takes one step (an op that picks its callee, two: below), a
  callee gets the steps its caller has left and
  gives back the rest, and the recursion is well-founded on the budget. Fuel
  must not change what a program means, nor any result of `fir-ref`.
- **A callee picked when the op runs** (#235). The op's rule maps its
  operands to a symbol, or is UB, given the module's test of which symbols
  take the call's types; the call then runs like a direct call on the
  operands but the first (ruled 2026-11-19, #235 Q2). The step count is
  not part of that ruling: the rule takes the op's step and the call one
  more, so that every step a traced run shows costs a step of fuel.
- **A call to a declaration** goes to the external-call rule, a part of the
  semantics of its own (ruled 2026-11-21, #239 Q1).

This is S7 of the fir v0 decision record, agreed on 2026-10-29 (#5). The
human chose fir's own calculus on 2026-10-29 (PR #27), and ruled on
2026-11-02 (#70) that the budget interface is designed before the run
theorems are proved.
[semantics-interpreter.md](../decisions/semantics-interpreter.md) states
what holds.

## Why

fir needs one definition that runs, as a test oracle, and that is a
mathematical object, so rewrite rules and the parser can be proved against
it. Lean is both. A Lean function must terminate, and fir programs may loop.

## Rejected alternatives

- **Interaction trees,** as in Vellvm. A fuelled interpreter is a total
  function that Lean runs directly and that proofs unfold case by case.
- **Depend on or fork LeanMLIR.** It has no CFG, op locations or value
  names, its parser cannot serve fir, and it is frozen on a Lean nightly.
- **VeIR.** Its coinductive choice trees conflict with this decision, and it
  stubs out locations and has no value names.
- **Fuel in a state monad, or a call effect on the monad.** Fuel
  monotonicity would be about the wrong counter, and the set monad has no
  module.
- **A separate op, `call_extern`,** which an indirect call (#235) could
  not use.
- **The interpreter resolving pointers itself, or a chain of fixed calls,**
  for an indirect call (#235 Q2): the first needs UB of the interpreter's
  own, the second makes an op's meaning depend on the whole table.
- **The rule and the call in one step:** a picked external call would show
  two steps for one step of fuel, and the bound of a traced run's fuel by
  its steps would fail.
