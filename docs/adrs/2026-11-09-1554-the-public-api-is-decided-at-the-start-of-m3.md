# The public API's shape is decided at the start of M3

Status: accepted
Tier: direction; area: process

## Context

P2, the shape of funk's public API, is deferred in the roadmap until
"before external users build on funk". M3's Vow frontend is the first such
user. M1 settles the IR contract, which is the text format and the spec;
the Rust API is a separate contract. The human ruled on
[#204](https://github.com/pmatos/funk/issues/204) on 2026-11-09.

## Decision

P2 is decided at the start of M3, before Vow frontend work begins, as a
`human-ready` issue on M3's epic. Until then the Rust API may change freely.

## Consequences

- M1 and M2 do not design for API stability.
- The first real user shapes the API.
