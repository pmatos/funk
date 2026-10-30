# fir test texts

Texts that both fir parsers read: `funk-ir` in Rust (#9) and the Lean spec's
parser, `Fir.parse`, through `fir-ref` (#10).

- `canonical/` holds canonical texts: each file is exactly the text that the
  printer writes, with no comments. For each, `print(parse(t)) == t`.
- `noncanonical/` holds inputs with comments, extra whitespace or other
  layout. Each `noncanonical/NAME.fir` parses to the same module as
  `canonical/NAME.fir`, which is its canonical form.

The Rust tests check both directories (`crates/funk-ir/tests/corpus.rs`).
`scripts/check-fir-ref.sh test` checks them with `fir-ref fmt`, and that
`fir-ref validate` accepts each one, as every text here is valid; it also
runs their functions with `fir-ref run` and checks each result
(ADR-2026-10-30-1856). `scripts/check-fir-ref.sh round-trip` has Lean
reprint what Rust prints from them, byte for byte (ADR-2026-10-30-1250).

The files use only the ops that the registry has: `const`, `add` and `ret`.
Texts that a parser must reject, and inputs that the repository's hooks
would change, such as a text without a final line feed or with a carriage
return, are written as escaped strings in the tests
(`crates/funk-ir/tests/` and `lean/FirTest/`), not as files.
