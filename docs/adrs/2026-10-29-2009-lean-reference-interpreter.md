# fir's semantics is a monadic definitional interpreter in Lean, with fuel

Status: accepted

## Context

This is decision S7 of the fir v0 decision record, agreed on 2026-10-29 and
stated in the M0 epic ([#5](https://github.com/pmatos/funk/issues/5)).

fir needs one definition of what a program means. That definition must run, so
that tests can use it as an oracle, and it must be a mathematical object, so
that rewrite rules and the parser can be proven against it. Lean is both a
programming language and a proof assistant. A Lean function must terminate,
and fir programs may loop forever.

## Decision

- The semantics of fir is a monadic definitional interpreter, written in Lean.
- Fuel bounds every run, so the interpreter always terminates. A run that uses
  all its fuel ends with fuel exhausted.
- It is not built on interaction trees.
- It is the **only** interpreter: a test oracle for development and CI, run as
  `fir-ref`. It never ships inside a compiler.
- Lean holds the semantics, the interpreter and its own `.fir` parser and
  printer. Rust holds the whole toolchain: the IR library, verifier, passes,
  backends and driver.
- There is no Rust interpreter in M0. A Rust evaluator may come later if
  fuzzing throughput or the JIT needs one, and then only as a copy tested
  against Lean, never as the definition.

Whether these Lean definitions build on LeanMLIR's SSA framework or on fir's
own calculus is not decided here. The spike in
[#24](https://github.com/pmatos/funk/issues/24) proposes an answer, and the
human decides.

## Alternatives

- **Interaction trees** (as in Vellvm). Rejected for a fuelled monadic
  interpreter, which is a total function that Lean runs directly and that
  proofs unfold case by case.

## Consequences

- Hand-written Rust, such as the backend, is checked against this
  interpreter, so the interpreter's speed bounds how much the harness can
  test.
- Fuel exhaustion is an outcome of its own, beside a value, poison and UB. It
  stands for non-termination.
- Lean and Rust each have a parser and a printer, and the text format must
  make them agree byte for byte (P3, ADR-2026-10-29-2014).
- The monad gets a choice effect for `freeze` (ADR-2026-10-29-2017).
