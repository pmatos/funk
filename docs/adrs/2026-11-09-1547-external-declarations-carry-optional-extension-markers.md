# An external declaration gives a signature that may be variadic, and narrow integers may carry `sext` or `zext`

Status: accepted
Tier: direction; area: semantics

## Decision

- **An external declaration** gives a symbol and a signature, and no body. A
  call to it is an observable event (ADR-2026-11-09-1540).
- **Variadic.** Its signature may end in `...`, and a call to it passes extra
  arguments after the fixed ones. Defining a variadic fir function stays out
  of M1 (ADR-2026-11-09-1548).
- **Extension markers.** An integer parameter or result narrower than 32
  bits, in a declaration or in a function's own signature, may carry `sext` or
  `zext`. A marked parameter is extended by the caller and the callee may rely
  on it. A marked result is extended by the callee and the caller may rely on
  it. With no marker nothing is guaranteed, and neither side may rely on the
  upper bits.
- **Validation.** The verifier rejects a marker on a type that is not an
  integer narrower than 32 bits.
- Frontends set the markers to match the C ABI.

[semantics-m1-design.md](../decisions/semantics-m1-design.md) states each
rule. The human ruled this on 2026-11-09, on #209.

## Why

Code that funk did not compile expects an `i8` or `i16` argument extended as
its C type requires, and fir types carry no sign, so such a call needs a
marker (ADR-2026-10-30-1232). A call between funk functions extends nothing
([x86-64-backend-abi.md](../decisions/x86-64-backend-abi.md#calls-between-funk-functions)).
Variadic declarations let funk call C, including `printf`.

## Rejected alternatives

- **Markers required on every narrow parameter.** Noisy for every caller that
  is not C, which has no use for them.
