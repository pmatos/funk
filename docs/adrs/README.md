# Architecture Decision Records

One file per decision, named `docs/adrs/YYYY-MM-DD-HHMM-slug.md` with the UTC
time (24h clock) it was written. Refer to one as `ADR-YYYY-MM-DD-HHMM`.

Timestamps, not sequence numbers: concurrent PRs collide when each picks "the
next number", but two authors do not pick the same minute independently.

## How to write one

- **One decision per ADR.** If you need "and also", write two.
- **Concise.** Most ADRs fit on one screen. Cut anything a reader does not need
  to understand or apply the decision.
- **Clear terms.** Plain words, short sentences, concrete names (files, flags,
  types). State the decision as a fact, not a hope; no hedging, no filler.
- **Written for a cold reader.** Assume no access to the conversation that led
  here: say what was decided, why, and what it costs.
- **Immutable once accepted.** To change a decision, write a new ADR and set the
  old one's status to `superseded by ADR-…`. Fix typos freely.

## Template

```markdown
# <The decision, stated as one sentence>

Status: accepted

## Context

The problem and the forces behind it: facts and constraints only.

## Decision

What we do, concretely enough to check whether code follows it.

## Alternatives

Optional. Each serious option we rejected, and why, in a line or two.

## Consequences

What becomes easier, what becomes harder, what we gave up.
```
