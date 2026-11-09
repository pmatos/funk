# Architecture Decision Records

One file per decision, named `docs/adrs/YYYY-MM-DD-HHMM-slug.md` with the UTC
time (24h clock) it was written and a slug of lower-case words joined by
hyphens. Refer to one as `ADR-YYYY-MM-DD-HHMM`.

When an ADR already holds that minute, the newer one adds the seconds:
`docs/adrs/YYYY-MM-DD-HHMMSS-slug.md`, referred to as `ADR-YYYY-MM-DD-HHMMSS`.
The id is the whole timestamp, and no two ADRs share one.

Timestamps, not sequence numbers: concurrent PRs collide when each picks "the
next number". A minute is rarer to share, but parallel agents shared one:
#34 and #35 both wrote an ADR at 2026-10-30 10:31. So the `adr-ids`
pre-commit hook rejects a misnamed ADR and two ADRs with one id, and CI runs
it on each PR's merge with `main` (ADR-2026-10-30-1329).

## How to write one

- **One decision per ADR.** If you need "and also", write two.
- **Concise.** Most ADRs fit on one screen. Cut anything a reader does not need
  to understand or apply the decision.
- **Clear terms.** Plain words, short sentences, concrete names (files, flags,
  types). State the decision as a fact, not a hope; no hedging, no filler.
- **Written for a cold reader.** Assume no access to the conversation that led
  here: say what was decided, why, and what it costs.
- **Immutable once accepted.** To change a decision, write a new ADR and set the
  old one's status to `superseded by ADR-…`. Fix typos freely. The status
  paragraph, its `Tier:` line included, is metadata and may change.

## When not to write one

Write an ADR for a decision that binds more than one module, or that a future
agent would otherwise rediscover or undo by accident. Implementation detail
that only one module needs goes in that module's doc comment.

To decide, ask whether someone changing a different module needs to know the
decision. If not, and the reason fits in the doc comment beside the code, write
the doc comment. Choices of how a single tool does one thing, such as a lookup
structure or which flag a helper takes, belong there.

## Tier and area

The last line of each ADR's status paragraph is `Tier: TIER; area: AREA`
(ADR-2026-11-09-1610).

- The tier is `direction` when the ADR says what fir is or sets a rule that
  every change follows, and `implementation` when it says how one tool does one
  thing.
- The area is one of `semantics`, `text-format`, `validation`, `fir-ref`,
  `rust-ir-and-tools`, `x86-64-backend`, `testing-and-harness`, `spec-site` and
  `process`.

[`INDEX.md`](INDEX.md) lists every ADR with its tier, area and what holds now.
It is generated, so never edit it by hand. After changing an ADR's title, status
or tier line, stage the ADR and run `python3 scripts/adr_index.py --write`. The
`adr-index` hook fails when the index is stale or an ADR has no tier and area.

## Published with the spec

The spec's appendix renders each ADR as a page, and every ADR citation in
the spec and the ADRs links to it (ADR-2026-10-30-1439). So:

- Start with the decision as a level-1 heading, then the `Status:` line, as
  the template does.
- Cite an ADR as plain text, `ADR-` and its id. In backticks it is an
  example, not a citation, and is not linked.
- Cite an ADR in the text, not in a heading or in a link's text: neither
  can hold the link, and the build fails, naming where.
- Link a file of the repository by its path relative to `docs/adrs/`.
- The spec build fails on a citation of an ADR that does not exist, and on
  Markdown the appendix cannot show: raw HTML, images, horizontal rules,
  strikethrough, task lists and hard line breaks.
- The `adr-citations` hook fails on a citation of an ADR that does not
  exist in any tracked text file, outside code (ADR-2026-11-05-1709).

## Template

```markdown
# <The decision, stated as one sentence>

Status: accepted
Tier: direction; area: process

## Context

The problem and the forces behind it: facts and constraints only.

## Decision

What we do, concretely enough to check whether code follows it.

## Alternatives

Optional. Each serious option we rejected, and why, in a line or two.

## Consequences

What becomes easier, what becomes harder, what we gave up.
```
