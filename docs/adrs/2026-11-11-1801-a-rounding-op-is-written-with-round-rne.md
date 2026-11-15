# A float op that rounds is written with round(MODE), and validation accepts only rne

Status: accepted
Tier: direction; area: text-format

## Decision

- `fadd`, `fsub`, `fmul`, `fdiv`, `sqrt`, `fma`, `sitofp`, `uitofp` and
  `fptrunc` round, and each has exactly one attribute, its rounding mode,
  in the applied form: `%s: f32 = fadd round(rne) %a, %b @1`.
- `frem`, `fmod`, `fneg`, `fabs`, `fpext`, `fptosi` and `fptoui` do not
  round, and have no attribute: `%n: f32 = fneg %a @1`.
- **Where a wrong mode is rejected** (the human's ruling of 2026-11-15 on
  #229, option B): every mode decodes, and validation (`Op.Valid`, and the
  verifier in Rust) rejects every mode but `rne`. So
  `fadd round(rtz) %a, %b` parses and is a validation error. The op carries
  its mode (`Fir.Core.RoundingMode`), as a load carries its ordering, and
  the rules read every mode as `rne`, since no valid module carries
  another.
- Everything else does not decode, and is a parse error
  (ADR-2026-10-29-2014): no attribute on an op that rounds, a word that
  names no mode (`round(up)`, `round(RNE)`), `round()`, `round(rne, rtz)`,
  the bare word `rne`, two attributes, and `round(rne)` on an op that does
  not round.
- **The mode words** are IEEE 754's five rounding-direction attributes
  (§4.3), in SMT-LIB's short names, lower case: `rne` (roundTiesToEven),
  `rna` (roundTiesToAway), `rtp` (roundTowardPositive), `rtn`
  (roundTowardNegative) and `rtz` (roundTowardZero). This set is an
  agent's proposal awaiting the human, put to them on the PR that makes
  this change; this ADR is edited in place if the human rules otherwise.

## Why

ADR-2026-11-09-1549 says every rounding op carries `round = rne`, that
round to nearest even is the only mode M1 accepts, and that rounding is an
attribute so that other modes can come back without a format break.
Decoding every mode makes that hook real: a later mode needs a rule and a
change of validation, not of the text reader, as the atomic orderings do
(ADR-2026-11-09-1542). Every rounding op of a text says how it rounds, so
today's texts keep their meaning when another mode comes. IEEE 754 names
exactly five directions, and `rne` and `rtz` were already the words of
this format's examples.

## Rejected alternatives

- **Only `rne` decodes, and a wrong mode is a parse error** (option A, as
  first built): a second mode would change the text reader as well as
  validation. The human ruled B on 2026-11-15.
- **No attribute, with round to nearest even implied.** It drops the hook
  that ADR-2026-11-09-1549 keeps, and a later mode would change the meaning
  of today's texts.
- **The word `rne` alone.** Shorter, but it says nothing about what it sets,
  and a later attribute of another kind would be ambiguous.
