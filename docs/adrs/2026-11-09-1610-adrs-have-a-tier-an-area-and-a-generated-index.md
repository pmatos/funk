# ADRs carry a tier and an area, a generated index lists them, and area pages say what holds

Status: accepted
Tier: direction; area: process

## Context

`docs/adrs/` holds 131 ADRs written in 12 days. The decisions that bind an
agent are lost among records of how one tool does one thing. What holds is
spread over chains of `refined by` status lines. The M0 close-out audit asked
for tiers and an index (#170). The human ruled on 2026-11-09: tiers, a
generated index, a rule for when not to write an ADR, and one page per area
that says what holds today.

## Decision

Every ADR ends its status paragraph with one line, `Tier: TIER; area: AREA`.
This is metadata, as the status line is, so adding or correcting it does not
break immutability.

The tier follows one test.

- `direction`: what fir is, or a rule that every change follows. A change to
  another module or tool would be bound by it.
- `implementation`: how one tool does one thing.

The area is one of nine: `semantics`, `text-format`, `validation`, `fir-ref`,
`rust-ir-and-tools`, `x86-64-backend`, `testing-and-harness`, `spec-site` and
`process`. An ADR that spans areas sits where a reader would look for it. So
G0's enforcement sits with G0 in `semantics`, and a CLI's report format sits
with its tool.

`scripts/adr_index.py --write` generates `docs/adrs/INDEX.md`, with one line
per ADR: its tier, area, title and what holds now. What holds now is the ADR
and every ADR that its `refined by` and `extended by` links reach, so a reader
need not follow a chain. A superseded ADR shows what holds of its successor.
The `adr-index` hook fails when the index is stale or an ADR has no
tier and area. `INDEX.md` is generated and over 20,000 bytes, so the
file-size hook excludes it.

`docs/decisions/` will hold one page per area in plain prose, each citing the
ADRs it rests on. A page that outgrows the file-size budget continues in a
sibling, `AREA-TOPIC.md`. ADRs stay immutable, and the pages only summarize
them. When a page and an ADR disagree, that is a bug in the page. The pages
land after this ADR. With them, the index links each ADR to its page, and the
hook also fails when no page of an accepted ADR's own area cites it.

Implementation detail that only one module needs goes in that module's doc
comment, not in a new ADR. `docs/adrs/README.md` says how to decide.

## Consequences

An agent starting cold can find the direction decisions in one table. Each new
ADR costs one more line and one more hook run. An ADR's tier is a judgement
call, recorded where it can be corrected.
