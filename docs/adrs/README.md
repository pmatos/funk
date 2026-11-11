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

## The pages are the record

Each area has a page in [`docs/decisions/`](../decisions/), `AREA.md`, that says
what holds today and cites the ADRs it rests on. A page that outgrows the file
size budget continues in a sibling, `AREA-TOPIC.md`. The page is the record:
when a page and an ADR disagree, the page wins, and the ADR is fixed or deleted.

- Each direction rule on a page keeps one line on the main alternative that was
  rejected, and why, so that no agent proposes it again.
- A rule that the human ruled says so on the page, with the date, also when the
  ADR that recorded the ruling is deleted or folded into another.
- A PR that adds or changes a direction ADR updates its area page in the same
  PR.

## When to write one

Write an ADR only for a direction decision that binds more than one module, or
a future dialect or target. These do not get an ADR; they go in the module's
doc comment or on the area page:

- how a proof is structured inside;
- following an external standard that the code already follows, such as an ABI
  or IEEE 754;
- a choice that the next PR of the same ticket may revise;
- how one tool does one thing, such as a lookup structure or a helper's flag.

To decide, ask whether someone changing a different module, dialect or target
needs to know the decision. If not, write the doc comment.

CI warns, without failing, when a pull request adds more than two ADRs, so that
the reviewer looks again at each one (`scripts/check_adr_ids.py
--warn-added`).

## How to write one

- **One decision per ADR.** If you need "and also", write two.
- **Three sections:** Decision, Why and Rejected alternatives, with no
  narrative context. About 300 words.
- **Clear terms.** Plain words, short sentences, concrete names (files, flags,
  types). State the decision as a fact, not a hope; no hedging, no filler.
- **Written for a cold reader.** Assume no access to the conversation that led
  here.
- **Edited in place.** When a decision changes, edit its ADR and its area page
  in the same PR; git keeps the history. There are no refining ADRs and no
  `superseded` status, and `adr_index.py` rejects a status that does not start
  with `accepted`. Older ADRs still carry `refined by` and `extended by`
  links until #307 folds each chain into one ADR.

## Deleting one

Delete the file and add a row to [`removed.json`](removed.json): the file's
name, where its rule lives now, and the last commit on `main` that changed the
file, `git log -1 --abbrev=12 --format=%h origin/main -- docs/adrs/FILE`. A
commit of the pull request's branch would not do: the squash merge leaves it
off `main`. Where its rule lives
is an ADR, `ADR-…`, or a page section, `docs/decisions/PAGE.md#ANCHOR`. Rewrite
every citation of the deleted id in the same PR, in code, tests, the spec and
the pages.

The rows become the Removed table of [`INDEX.md`](INDEX.md). The `adr-ids` hook
never lets a removed id be used again. A citation of a removed id fails the
`adr-citations` hook and the spec build, and the message names where the rule
lives now.

## Tier and area

The last line of each ADR's status paragraph is `Tier: TIER; area: AREA`
(ADR-2026-11-09-1610).

- The tier is `direction` when the ADR says what fir is or sets a rule that
  every change follows, and `implementation` when it says how one tool does one
  thing.
- The area is one of `semantics`, `text-format`, `validation`, `fir-ref`,
  `rust-ir-and-tools`, `x86-64-backend`, `testing-and-harness`, `spec-site` and
  `process`.

[`INDEX.md`](INDEX.md) lists every ADR with its tier, area and what holds now,
then the Removed table. It is generated, so never edit it by hand. After
changing an ADR's title, status or tier line, or `removed.json`, stage the
change and run `python3 scripts/adr_index.py --write`. The `adr-index` hook
fails when the index is stale, an ADR has no tier and area, an ADR is cited by
no page of its area, or a row of `removed.json` names an ADR or page section
that does not exist.

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

## Decision

What we do, concretely enough to check whether code follows it.

## Why

The facts and constraints that make this the right choice.

## Rejected alternatives

Each serious option we rejected, and why, in a line or two.
```
