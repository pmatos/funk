# Agents wait for human rulings before changing agreed direction

Status: accepted

## Context

The M0 close-out audit found agents choosing answers to direction questions
while the human was away, widening tickets and starting work against the
human's ordering. Recording those choices afterward did not authorize them.
The human approved the three rules proposed in
[#171](https://github.com/pmatos/funk/issues/171) on 2026-11-06.

## Decision

Every agent, including an orchestrator, follows this approval boundary:

- An unanswered direction question waits in a `human-ready` issue. A timeout
  or the human's absence never supplies an answer. Continue independent work.
- Ambition means finishing the agreed ticket scope. File additional work
  separately and obtain the human's ruling before widening the ticket.
- Ask before starting a new performance or scale ticket, or introducing new
  tooling or checking machinery, including hooks and verifiers.

Routine implementation choices, such as naming and test details, may proceed
within the ticket's scope and must be recorded. Existing authorized checks
can proceed. [AGENTS.md](../../AGENTS.md) holds these standing rules.

## Consequences

Work that depends on a direction ruling may wait while independent work
continues. A cold-starting agent can distinguish a human ruling from an
implementation choice without treating silence as approval. The PR and merge
rules of ADR-2026-10-28-0725 and ADR-2026-11-03-1612 continue to apply.
