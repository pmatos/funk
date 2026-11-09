# The fir explorer is a local Python server over funk and fir-ref

Status: accepted
Tier: implementation; area: testing-and-harness

## Context

The human asked on 2026-11-08 for a web app, run locally in the manner of
Compiler Explorer, to write fir and see what it compiles to and what it means
([#216](https://github.com/pmatos/funk/issues/216)). The semantics of fir lives
in Lean, and the judgement of a native run lives in the harness's Python
(ADR-2026-11-06-1218). The app compiles and runs whatever is typed into it.

## Decision

- **Where it lives.** The package `scripts/harness/explorer/`, started by
  `scripts/explorer.sh`. It imports the harness's modules, and the existing
  `fir-harness-test` hook runs its tests, so it adds no hook.
- **No dependencies and no build step.** The server uses Python's standard
  library. The page is static HTML, CSS and JavaScript modules, with nothing
  loaded from elsewhere.
- **No semantics of its own.** It runs `funk` and `fir-ref` and shows what they
  report. A verdict on a native run comes from `differential.evaluate`.
  It says that a native run is unavailable, and raises no alarm, when the
  backend cannot lower the module or `fir-ref` cannot run the call.
- **Reachable only from this machine.** It binds to the loopback address, with
  no option to change that. Every request must name a loopback `Host`, which
  stops DNS rebinding. Every POST must carry the page's own `Origin` and be
  `application/json`, so another web page in the browser cannot run code.
- **One request at a time.** Native runs use `preexec_fn`, which is not safe
  with threads.
- **Limits.** Native runs keep the harness's data limit (ADR-2026-11-02-2250).
  Each tool and native program has 10 seconds by default, set by `--timeout`.

## Alternatives

- **A Rust server.** It would need a web dependency, and a second copy of the
  harness's judgement or a way to call it.
- **A front-end framework and an editor library.** They bring a build step and
  dependencies, for one local page.

## Consequences

- A long native run holds up the other requests until its timeout.
- The app grows with the tools: a new `fir-ref` result needs decoding here.
- The harness's process mechanics are shared, so a change to them reaches the
  explorer.
