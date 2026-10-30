# A value of iN lives in the low N bits of a 64-bit register or slot; the bits above are unspecified

Status: accepted

## Context

[#12](https://github.com/pmatos/funk/issues/12) asks the backend to lower
`i1`, `i8`, `i16`, `i32` and `i64` from the start, so that later op
families do not reinvent how widths are handled. `i128` comes with
register pairs in #21. fir types have no sign: signedness lives on ops
(S2, ADR-2026-10-29-2007). System V leaves the bits above a narrow result
unspecified. C compilers expect more of a narrow argument than that
(ADR-2026-10-30-1232).

## Decision

- **The low bits are the value.** A value of `iN`, `N` at most 64, lives in
  one 64-bit register or slot. Its low `N` bits are its bits; the bits
  above them are unspecified. The same rule holds in slots, in scratch
  registers, for the arguments a funk function receives and for the
  results it returns. What a caller extends before it calls code that funk
  did not compile is in ADR-2026-10-30-1232.
- **Extend where the high bits matter.** An op whose result's low `N` bits
  depend only on its operands' low `N` bits (`add`, `sub`, `mul`, `and`,
  `or`, `xor`, `trunc`, `select`, `freeze`) works on all 64 bits and needs
  no extension. An op that reads more (comparisons, division, `zext`,
  `sext`, the value of a right shift, and the amount of every shift) first
  extends those operands with `width::extend`, by sign or by zero as the op
  reads them. A branch or a `select` on an `i1` tests bit 0.
- **Supported widths.** `width::check` accepts `i1`, `i8`, `i16`, `i32` and
  `i64`. Every other width is reported as unsupported where its value is
  defined: a parameter at its function's entry block, a result at its op.
  `i128` gets its own message until #21; every width outside the six is
  always rejected.

## Alternatives

- **Keep every value sign-extended to 64 bits.** Comparisons would need no
  extension, but every arithmetic op would need one after it, and values
  that come from C would still have to be extended on entry.
- **Sized instructions** (`addb`, `cmpw`, `idivl`). They fit `i8` to
  `i64`, but `i1` has no register of its own, and the bits-above rule
  would still be needed at calls.

## Consequences

- `add` at every width is one `addq`.
- Each later op family must say, in its lowering, which operands it
  extends and how. `width::extend` is the one place that knows the
  instructions.
- A result printed or compared outside the backend, such as by the
  executable's entry point, is extended first.
