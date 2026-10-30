# In the Lean tests, the sum of the core dialect and a test dialect sends op names that start with `toy.` to the test dialect

Status: accepted

## Context

G0 (ADR-2026-10-29-2016) requires that a new dialect need no change to the
interpreter, the parser or the printer.
[#10](https://github.com/pmatos/funk/issues/10) asks for a test-only
dialect that shows it in Lean, and for a module that mixes core ops and a
toy op. The spec's classes take one dialect, so such a module needs one
dialect that holds both: a sum of the two, with each class lifted to it.

Reading an op calls `decodeOp` with the op's name, attributes and types.
`LawfulDialectText` asks that decoding what was written gives the op back.
If the sum sends each name to one side, an op whose name goes to the other
side cannot be read back, so the sum's text is lawful only when the two
sides' op names are disjoint.

ADR-2026-10-30-1146 names the ops and types of a test dialect `toy.` and a
word, such as `toy.br`. `.` is reserved for a dialect's name before its ops
(H4), and no core op name holds one. That ADR routes `toy.` names to the
test dialect in `funk-ir`'s registry and asks Lean to do the same. How real
dialects name their ops and are combined is H4, which is not decided.

## Decision

- **A sum over shared types.** `FirTest.SumDialect Ty Op₁ Op₂`
  (`lean/FirTest/Sum.lean`) holds the ops of the dialects `⟨Op₁, Ty⟩` and
  `⟨Op₂, Ty⟩`, which share the types `Ty`. The second dialect adds ops over
  the first's types, as a toy op works on core integers. The sum lifts
  `DialectSignature`, `DialectText`, `DialectValidation`,
  `DecidableDialectValidation`, `DialectPoison` and `DialectDenote`: each
  op has its own dialect's signature, text, rules, poison class and
  semantics, and the types have the first dialect's text and validity.
- **Routing by name alone.** `decodeOp` sends a name to the second dialect
  when the class `SumRoute Op₁ Op₂` says so, and every other name to the
  first, and only that side decodes it.
- **When the sum is lawful.** Given two dialects with lawful text, the sum's
  text is lawful exactly when every op name goes to its own side
  (`SumDialect.lawful_iff`), and so only when no op name belongs to both
  sides (`SumDialect.names_disjoint`).
- **The rule for test dialects.** A test dialect names its ops `toy.` and a
  word. The sum of the core dialect and a test dialect sends each name that
  starts with `toy.` to the test dialect, and every other name to the core
  dialect (`FirTest.isToyName`). The core dialect's 24 op names never start
  with `toy.`, so the sum of the core and the toy dialect is lawful.
- **Test-only.** The sum, the toy dialect and this rule live in
  `lean/FirTest/`, not in the spec. They decide nothing about H4.

## Alternatives

- **Summing the types too**, `Ty₁ ⊕ Ty₂`. A toy op could then not take a
  core value, and the sum would also need the two sides' type names
  disjoint. A dialect's rules see the module's symbol table in their own
  types, which a sum of types cannot always give them.
- **Trying the first side, then the second.** A name would then reach a
  side by its attributes and types as well, so two dialects could share an
  op name and still read back. #10 asks that `decodeOp` send each name to
  one side, and `funk-ir` routes by the name alone.
- **The sum in the spec.** It would say how dialects combine, which is H4.

## Consequences

- A test that mixes core ops and toy ops parses, prints, validates and
  runs a module of `FirTest.CoreToy` with the spec's parser, printer,
  validation check and interpreter, unchanged.
- The sum of the core and the toy dialect gets the spec's round-trip
  results that rest on `LawfulDialectText`, such as `validIsWellFormed`.
- When H4 decides how real dialects name their ops and combine, it may
  move a sum into the spec, with its own routing rule. This rule stays the
  rule for test dialects.
