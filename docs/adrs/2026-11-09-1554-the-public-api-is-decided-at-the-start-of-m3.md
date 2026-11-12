# The public API's shape is decided at the start of M3

Status: accepted
Tier: direction; area: process

## Decision

P2, the shape of funk's public API, is decided at the start of M3, before Vow
frontend work begins, as a `human-ready` issue on M3's epic. Until then the
Rust API may change freely, and M1 and M2 do not design for API stability.

The human ruled this on 2026-11-09, in #204.

## Why

M3's Vow frontend is the first user that builds on funk, so the first real
user shapes the API. M1 settles the IR contract, which is the text format and
the spec; the Rust API is a separate contract.

## Rejected alternatives

- **Decide P2 in M1, with the IR contract.** The two contracts are separate,
  and no user would yet build on the Rust API.
- **Leave P2 "before external users build on funk".** The roadmap's old
  wording named no point at which the question is asked.
