# The round trip is fuzzed over well-formed modules, and across languages over those of the core dialect only

Status: accepted
Tier: implementation; area: testing-and-harness

## Context

P3's round trip holds for every well-formed module (ADR-2026-10-30-0815),
a larger set than the valid modules that `generate::module` makes. Issue
#146 found that no fuzzing reached the rest: ops that own regions, string
and applied attributes, fused locations of fewer than two references,
unreachable blocks, undefined successors and callees, and broken location
tables. The human decided in triage on 2026-11-05 to fuzz them in Rust and
across languages, with `fir-ref fmt` reprinting each text without
`fir-ref validate` accepting it first.

`fir-ref` parses with the core dialect only (`lean/FirRef/Main.lean`). No
core op and no core type decodes a string or applied attribute
(`Core.Op.decode` and `Core.Ty.decode` in `lean/Fir/Core/Text.lean`), so no
core module holds one, and a text with an op of another dialect does not
parse in `fir-ref`.

## Decision

- `generate::wellformed::module` makes well-formed modules that validation
  mostly rejects, from a valid module of `generate::module`, which stays as
  it is. It takes `Dialects::Core` or `Dialects::CoreAndToy`.
- `Dialects::CoreAndToy` adds `toy.any`, the op of the test dialect
  `generate::wellformed::toy_dialect`, which decodes with any attributes,
  operands, results and regions. String and applied attributes are only on
  it.
- `Dialects::Core` puts regions on core ops: they decode, and validation
  rejects them, as it rejects a region on any op in v0.
- `crates/funk-ir/tests/wellformed.rs` checks `parse(print(m)) == m` and
  `print(parse(t)) == t` on the first `WELL_FORMED_MODULES` (600) modules
  of each kind, and that each shape of #146 is in at least a tenth of them.
- `scripts/check-fir-ref.sh round-trip` has the example
  `fir_wellformed_texts` print the first 600 `Dialects::Core` modules, and
  `fir-ref fmt --check` must reprint each one byte for byte. Nothing
  validates them.

## Consequences

- Across languages, string and applied attributes and ops of other
  dialects are not fuzzed: `fir-ref` cannot read them. Rust fuzzes them,
  and Lean proves the round trip for every lawful dialect
  (`printThenParse`).
- The new checks run in the existing `rust-test` and `fir-round-trip`
  hooks, so CI needs no new step.
- A change to `generate::module` changes the well-formed modules too.
