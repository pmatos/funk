# A float op that rounds is written with round(rne), and no other mode decodes

Status: accepted
Tier: direction; area: text-format

## Context

ADR-2026-11-09-1549 says every rounding op carries `round = rne`, and
that round to nearest even is the only mode M1 accepts. Rounding is an
attribute so that other modes can come back without a format break. An
attribute is a generic term: a word, an integer, a string, a symbol, a
float literal, or a word applied to attributes, as in `float(e, m)`
(ADR-2026-11-11-0951). The text has no `key = value` form, and each op
has one spelling (ADR-2026-10-29-2014).

## Decision

- `fadd`, `fsub`, `fmul`, `fdiv`, `sqrt` and `fma` round, and each has
  exactly one attribute, `round(rne)`, in the applied form:
  `%s: f32 = fadd round(rne) %a, %b @1`.
- `fneg` and `fabs` do not round, and have no attribute:
  `%n: f32 = fneg %a @1`.
- Any other attribute does not decode: no attribute on an op that rounds,
  `round(rtz)` or any other mode, the bare word `rne`, two attributes, or
  `round(rne)` on `fneg` or `fabs`. Text that does not decode is a parse
  error (ADR-2026-10-30-0815), so `funk verify` and `fir-ref` reject it,
  as they reject a flag that an op does not have.
- The op carries no mode: M1 has one, so the spec's op instances have no
  field for it. A later mode adds a decoding and a field.

## Alternatives

- **Decode every IEEE mode, and let validation reject all but `rne`.** It
  gives each op a field that no valid program sets and a rule for modes
  that have no meaning in M1.
- **No attribute, with round to nearest even implied.** It drops the hook
  that ADR-2026-11-09-1549 keeps, and a later mode would change the
  meaning of today's texts.
- **The word `rne` alone.** Shorter, but it says nothing about what it
  sets, and a later attribute of another kind would be ambiguous.

## Consequences

- Every rounding op of a text says how it rounds, so today's texts keep
  their meaning when another mode comes.
- A rounding mode that fir does not have is a parse error, not a
  validation error.
