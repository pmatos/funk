# Agents wait for human rulings before changing agreed direction

Status: accepted
Tier: direction; area: process

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
can proceed. [AGENTS.md](../../AGENTS.md) holds these standing rules. The PR
and merge rules of ADR-2026-10-28-0725 continue to apply.

The human approved these three rules as written on 2026-11-06, in #171.

## Why

The M0 close-out audit found agents choosing answers to direction questions
while the human was away, widening tickets and starting work against the
human's ordering. With these rules, a cold-starting agent can tell a human
ruling from an implementation choice without treating silence as approval.
Work that depends on a ruling may wait while independent work continues.

## Rejected alternatives

- **Decide, then record the choice afterward.** That is what the audit found:
  recording a direction choice afterward did not authorize it.
