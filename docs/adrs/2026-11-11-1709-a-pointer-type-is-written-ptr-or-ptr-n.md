# A pointer type is written ptr for the default memory, or ptr(N) for memory N

Status: accepted
Tier: direction; area: text-format

## Decision

- `ptr<0>`, the default memory's pointer (ADR-2026-11-09-1542), is written
  `ptr`, so M0's texts are unchanged.
- `ptr<N>` for `N ≥ 1` is written with the grammar's applied form, `ptr(N)`,
  with `N` in decimal, such as `ptr(1)`.
- `ptr(0)` does not decode, so each pointer type has one spelling. Neither
  does a negative memory, a memory above 16,777,215 (`2^24 - 1`, LLVM's bound
  on address spaces), `ptr()` or any other argument list.
- `ptr<N>` stays the notation of the spec's prose and the ADRs. It is not
  text.
- `ptr(N)` decodes for every `N` in range. Whether the module has memory `N`
  is validation's rule: every module has memory 0, and another memory exists
  only when the module's data layout declares it.
- `ptr(N)` is the core's. A dialect that adds memories of its own names their
  pointers in its own types, `name.word`.

## Why

fir has one canonical text, with one spelling for every construct
(ADR-2026-10-29-2014). The grammar writes a type as a word, or as a word
applied to attributes, and has no angle brackets; the float family is spelled
the same way (ADR-2026-11-11-0951). So both parsers read pointer types as any
type, and only the core dialect's decoding of types changes.

## Rejected alternatives

- **`ptr<N>` in text.** It needs angle brackets in the grammar of both
  parsers and new round-trip proofs, for one type family.
- **`ptr(0)` as a second spelling of `ptr`.** Two spellings break
  `print(parse(t)) == t` (ADR-2026-10-29-2014).
- **Rejecting `ptr(N)` of an undeclared memory at parse time.** A builder or
  a pass can change the module's data layout without text, so the rule is
  validation's.
