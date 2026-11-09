# The spec build pins module docs and requires every fir module

Status: accepted

## Context

ADR-2026-11-05-2012 makes the build fail when the Lean changes under a
readable block. Issue #195 listed four ways that the spec could still drift
from the code. ADR-2026-11-06-0744 requires the human's approval for new
checking machinery, and the human ruled on each gap on 2026-11-09.

## Decision

1. **A stale fingerprint forces a look, not a correct rewrite.** This stays
   with review. The PR template has a checkbox for it. No check looks for a
   change in the prose, because such a check would invite token edits.
2. **A block that restates a definition without pinning it goes unnoticed.**
   We accept this. Pins stay explicit, with no transitive hashing, as ruled
   on #161.
3. **Module docs are pinned.** Each readable document holds one
   `:::moduleDocs (fingerprint := "…")` directive when its Lean module has
   `/-! -/` docs. The fingerprint covers every declaration that the
   document's readable blocks explain, whatever their order. The build fails
   when a directive is missing or stale, and names the new value.
4. **Every module under `lean/Fir` is in the spec.** `firspec` fails when
   `docs/spec/FirSpec.lean` has no `{includeReadable}` or `{includeLiterate}`
   line for a module.

Both checks run in the `fir-spec` hook.

The module pin covers the code and not the text of the docs. A readable
block's fingerprint does not cover its prose either, and the point of the
pin is to catch code that changes under the docs.

A module that declares nothing, such as `Fir.Execution.PoisonUB`, has no pin.
A pin on its own code would cover nothing, and it has no readable document
to hold one (ADR-2026-11-05-225128). What it restates from other modules is
the same gap as point 2, which we accept.

## Consequences

- A change to what a module says needs two updates: the block's pin and the
  module's pin. A change to a proof needs neither.
- A module doc can restate a definition from another module without any pin
  covering it. This is the same gap as point 2.
- An edit to module docs alone needs no new pin.
