# Current decisions: semantics, external calls in M1

This page continues semantics-m1-trace.md, which says what an M1 run shows
and how the world answers it. It says how a call to an external declaration
runs, in each layer, and the conditions under which poison handed to the
world keeps the refinement theorems. It is the record: when this page and
an ADR disagree, the page wins, and the ADR is fixed or deleted
(ADR-2026-11-09-1610). ADR-2026-11-09-1540 holds the direction decision,
and ADR-2026-10-29-2009 the run's rule for a call.

## External calls

The human ruled on 2026-11-21, on #239, how an external call runs. The
spec states the core's events and its traced semantics op by op
(`lean/Fir/Core/Event.lean`, `lean/Fir/Core/Trace.lean`), and the run
hands a call to a declaration to the external-call rule
(`lean/Fir/Execution/ExtCall.lean`), UB in the layers with no world. Until
#239's next stage, the core's traced external-call rule is still its rule
with memory, lifted, so UB too, and validation still rejects a call to a
declaration, so no valid module reaches it. The rule that shows the event
and takes the world's answer is defined, not installed (below). #239's
stage 3b-2b makes it the core's and states the conditions of poison
handed to the world below; stage 3b-2c lets validation accept the call.

- **The core's traced rule, defined.** The spec defines the core's
  traced external-call rule (`lean/Fir/Core/ExtCallRule.lean`): the call
  lets escape what it reaches, shows its event from there, asks the
  world, and reads the reply back as its results, each pointer by its
  handle in the traced state the world's actions leave. A reply whose
  values do not have the call's result types, or that names a handle of
  no escaped allocation of the pointer's memory, is one the world cannot
  give, as an action it cannot take is, so the call has no outcome for
  it; a poison of each result type is always one it can give. The rule
  has finitely many outcomes given the world's answers, and is monotone
  when both calls let escape the same allocations in the same order. It
  is not yet the core's rule: #239's stage 3b-2b installs it. The reading
  of a reply is an agent's choice, made in stage 3b-2a, not a ruling.
  Rejected: read a bad handle as poison, which lets a reply that names no
  allocation stand for one that does.
- **One `call` op.** When `call` names an external declaration, the run
  hands the call to a new external-call rule of the dialect, given the
  symbol, the arguments and the result types. In the traced layer the
  core's rule shows the event and asks the world. An indirect call (#235)
  whose pointer names a declaration reuses it. Rejected: a separate op,
  `call_extern`, valid only on a declaration.
- **The layers with no world.** In the set-monad and memory layers an
  external call is UB, as a stand-in. Every guarantee with memory keeps
  its statement and stays true, but says nothing of code that calls
  outside the module: the traced guarantees are the ones that cover
  external calls. Rejected: any results and any memories, which breaks
  the finiteness that congruence in the callee needs; and guarantees
  with memory that cover only modules that call no declaration.
- **Congruence in the callee over traced runs** takes its hypothesis over
  traced runs from every traced state (`Func.traceRunsFrom`), the form the
  traced layer's own theorem takes. Rejected: the hypothesis with memory,
  plus no external call, volatile access or assembly block in either body
  of the callee.
- **Poison handed to the world.** Alive2's rule: a target may not let
  escape what the source did not, so refined arguments over traced runs
  gains that condition. Rejected: the call freezes the poison it hands
  out, which gives a call infinitely many outcomes; and handing poison to
  the world is UB, which an uninitialised buffer or struct padding passed
  to C would hit.
- **Poison handed to the world, in the callee.** Congruence in the callee
  over traced runs gains the condition that refined arguments gains: the
  new module may not let escape what the old one did not. The human ruled
  this on 2026-11-22, on #239 (Q5). Rejected: keep the theorem
  unconditional, and ask that the new callee hold no pointer wherever the
  old one returned or left poison.
- **What "the same" escapes means.** The no-new-escape condition of Q4
  and Q5 compares the escaped lists as ordered lists: the same
  allocations, in the same order, since the world names each by its
  place. The human ruled this on 2026-11-22, on #239 (Q6). Rejected: the
  same set of allocations plus a renaming of handles, which needs
  refinement of traces up to a permutation.
