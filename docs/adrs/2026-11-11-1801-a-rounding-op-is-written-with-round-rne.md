# A float op that rounds is written with round(MODE), and validation accepts only rne

Status: accepted
Tier: direction; area: text-format

## Decision

- Each float op that rounds (`fadd`, `fsub`, `fmul`, `fdiv`, `sqrt`, `fma`,
  `sitofp`, `uitofp`, `fptrunc`) has exactly one attribute, its rounding
  mode, in the applied form: `%s: f32 = fadd round(rne) %a, %b @1`. An op
  that does not round has none: `%n: f32 = fneg %a @1`.
- Every mode decodes, and validation rejects every mode but `rne` (the
  human's ruling of 2026-11-15 on #229, option B). So `fadd round(rtz)`
  parses and fails validation. The op carries its mode, as a load carries
  its ordering, and the rules read every mode as `rne`.
- Anything else is a parse error (ADR-2026-10-29-2014): no mode on an op
  that rounds, a word that names no mode, the bare word `rne`, two
  attributes, and a mode on an op that does not round.
- The mode words are IEEE 754's five rounding-direction attributes in
  SMT-LIB's short names: `rne`, `rna`, `rtp`, `rtn` and `rtz`. This set is
  an agent's proposal awaiting the human (#229); this ADR is edited in
  place if the human rules otherwise.

## Why

ADR-2026-11-09-1549 makes rounding an attribute so that other modes can
come without a format break. Decoding every mode makes that hook real: a
later mode needs a rule and a change of validation, not of the reader, as
the atomic orderings do (ADR-2026-11-09-1542). Every rounding op says how
it rounds, so today's texts keep their meaning when another mode comes.
IEEE 754 names exactly five directions, and `rne` and `rtz` were already
this format's words.

## Rejected alternatives

- **Only `rne` decodes** (option A, as first built): a second mode would
  change the reader as well as validation. The human ruled B.
- **No attribute, with round to nearest even implied:** it drops the hook,
  and a later mode would change the meaning of today's texts.
- **The word `rne` alone:** it says nothing about what it sets.
