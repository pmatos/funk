# A native run reports its globals, and the harness relates them by fir-ref's offsets

Status: accepted
Tier: direction; area: testing-and-harness

## Decision

- **The result format.** A built executable run as `OUTPUT --memory @f
  ARG...` prints its values line with one more field, `memory`, after
  `values`: every global of the module's own table, in the table's order,
  as `{"global":"@g","memory":N,"address":"A","units":"U"}`. `@g` is the
  global's name as fir's text writes it, `A` its address spelled as a
  pointer result is, and `U` its units, two lower-case hexadecimal digits
  each, with a run of 16 or more zero units written `zeros(N)`. Without
  `--memory` the output is byte for byte what it was. The harness passes
  `--memory` on every native run, and a line without the field, or with
  any other key, fails.
- **How the harness relates the two ends.** It judges the end of a native
  return against `fir-ref run --world`'s
  ([fir-ref-run-end.md](../decisions/fir-ref-run-end.md#how-a-judge-compares-two-ends)),
  by the same one-to-one renaming built from the source's side. A pointer of
  `fir-ref`'s into an allocation it lists, at offset `O`, is related to the
  native global whose address plus `O` is the native pointer's address:
  a returned pointer by its value, a stored one by its eight units, little
  endian. The related global must have the source's kind, size and
  liveness, an address that is a multiple of its alignment, and units that
  refine the source's. No native address is compared with `fir-ref`'s.
- **What it cannot relate.** A pointer with no provenance, returned or
  stored, a stored part of a pointer whose allocation nothing relates, and
  an id that `fir-ref`'s memory never made make the test invalid, unless
  native code refines another outcome.

The human ruled the option (#213, Q1 B) and reading a returned address
(#213, Q2 A) on 2026-11-22.

## Why

A wrong store into memory that an observer sees is what S4's refinement
must catch (ADR-2026-11-09-1540), and a run cannot tell which of its
bytes are pointers, so it reports every global and the harness, which
knows `fir-ref`'s end, relates them. The option keeps every existing
output, as `fir-ref run --world` does (#466). Runs of zeros keep a large
`.bss` global short.

## Rejected alternatives

- **Always print the field.** Every run's output changes, also where no
  global exists.
- **A wrapper function the harness generates.** It tests another module,
  and a large global exceeds the values a function returns.
- **No native memory report.** Native code is never checked for a wrong
  store that an observer sees.
- **Returned pointers stay opaque.** A test that returns a global's
  address stays interpreter-only.
