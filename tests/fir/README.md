# fir test texts

Texts that both fir parsers read: `funk-ir` in Rust (#9) and the Lean spec's
parser (#10).

- `canonical/` holds canonical texts: each file is exactly the text that the
  printer writes, with no comments. For each, `print(parse(t)) == t`.
- `noncanonical/` holds inputs with comments, extra whitespace or other
  layout. Each `noncanonical/NAME.fir` parses to the same module as
  `canonical/NAME.fir`, which is its canonical form.

The files use only the ops that the registry has: `const`, `add` and `ret`.
Texts that a parser must reject, and inputs that the repository's hooks
would change, such as a text without a final line feed or with a carriage
return, are written as escaped strings in the tests
(`crates/funk-ir/tests/`), not as files.
