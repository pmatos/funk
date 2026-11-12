# ADRs carry a tier and an area, a generated index lists them, and area pages are the record

Status: accepted
Tier: direction; area: process

## Decision

Every ADR ends its status paragraph with one line, `Tier: TIER; area: AREA`.
This is metadata, as the status line is.

The tier follows one test.

- `direction`: what fir is, or a rule that every change follows. A change to
  another module or tool would be bound by it.
- `implementation`: how one tool does one thing.

The area is one of nine: `semantics`, `text-format`, `validation`, `fir-ref`,
`rust-ir-and-tools`, `x86-64-backend`, `testing-and-harness`, `spec-site` and
`process`. An ADR that spans areas sits where a reader would look for it. So
G0's enforcement sits with G0 in `semantics`, and a CLI's report format sits
with its tool.

`scripts/adr_index.py --write` generates `docs/adrs/INDEX.md`, with one line per
ADR: its tier, area, title and what holds now. What holds now is the ADR and
every ADR that its `refined by` and `extended by` links reach, so a reader need
not follow a chain. The index ends with a Removed table, generated from
`docs/adrs/removed.json`: each deleted ADR's id, where its rule lives now, and
the last commit on `main` that changed its file. The `adr-index` hook fails when
the index is stale or an ADR has no tier and area. `INDEX.md` is generated and
over 20,000 bytes, so the file-size hook excludes it.

`docs/decisions/` holds one page per area in plain prose, each citing the
ADRs it rests on. A page that outgrows the file-size budget continues in a
sibling, `AREA-TOPIC.md`. The page is the record: when a page and an ADR
disagree, the page wins, and the ADR is fixed or deleted. Each direction rule
on a page keeps one line on the main rejected alternative, and a rule the human
ruled says so, with the date. The index links each ADR to its page, and the
hook also fails when no page of an ADR's own area cites it.

An ADR is edited in place when its decision changes, because git keeps the
history. There are no refining ADRs and no `superseded` status. A deleted ADR
gets a row in `removed.json`, its id is never used again, and a citation of it
fails with where its rule lives now.

Write an ADR only for a direction decision that binds more than one module, or
a future dialect or target. Its form is Decision, Why and Rejected
alternatives, in about 300 words. A proof's internal structure, an external
standard the code already follows, such as an ABI or IEEE 754, a choice the
next PR of the same ticket may revise, and implementation detail that only one
module needs go in the module's doc comment or on the area page.
`docs/adrs/README.md` says how to decide. CI warns, without failing, when a
pull request adds more than two ADRs.

The human ruled on 2026-11-09, in #170: tiers, a generated index, a rule for
when not to write an ADR, and one page per area that says what holds today. On
2026-11-11, in [#307](https://github.com/pmatos/funk/issues/307), the human
ruled that the pages are the record and that ADRs are cut down to short
direction decisions: "This is git - if we delete a file it's never lost."

## Why

`docs/adrs/` held 131 ADRs written in 12 days. The decisions that bind an
agent were lost among records of how one tool does one thing, and what held
was spread over chains of `refined by` status lines. The M0 close-out audit
asked for tiers and an index (#170).

An agent starting cold can find the direction decisions in one table, and
reads what holds on one page per area. Each new ADR costs one more line and one
more hook run. An ADR's tier is a judgement call, recorded where it can be
corrected. Deleting an ADR costs a row in `removed.json` and a rewrite of each
citation of it.

## Rejected alternatives

- **Pages that only summarize immutable ADRs.** They grew chains of refining
  ADRs that no one reads.
- **A new ADR for each change of a decision.** It made same-day
  write-then-supersede pairs.
