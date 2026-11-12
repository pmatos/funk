# An external declaration gives a signature that may be variadic, and narrow integers may carry `sext` or `zext`

Status: accepted
Tier: direction; area: semantics

## Context

ADR-2026-10-30-1232 says that code funk did not compile expects an `i8` or
`i16` argument extended as its C type requires, and an `i1` as 0 or 1, and
that fir types carry no sign, so such a call needs a marker.
A call between funk functions extends nothing, and the backend left the marker
to the ticket that lets fir declare such functions
([x86-64-backend-abi.md](../decisions/x86-64-backend-abi.md#calls-between-funk-functions)).
Under ADR-2026-11-09-1543 an external declaration is a kind of item.
ADR-2026-11-09-1548 puts calls to variadic external functions in M1. The human
ruled on [#209](https://github.com/pmatos/funk/issues/209) on 2026-11-09.

## Decision

- **An external declaration** gives a symbol and a signature, and no body.
  A call to it is an observable event (ADR-2026-11-09-1540).
- **Variadic.** Its signature may end in `...`. A call to it passes extra
  arguments after the fixed ones. Defining a variadic fir function stays
  out of M1 (ADR-2026-11-09-1548).
- **Extension markers.** An integer parameter or result narrower than 32
  bits, in a declaration or in a function's own signature, may carry `sext`
  or `zext`:
  - a marked parameter is extended by the caller, by sign or by zero, and
    the callee may rely on it;
  - a marked result is extended by the callee, and the caller may rely on
    it;
  - with no marker, nothing is guaranteed, and neither side may rely on
    the upper bits, as for calls between funk functions
    ([x86-64-backend-abi.md](../decisions/x86-64-backend-abi.md#calls-between-funk-functions)).
- **Validation.** The verifier rejects a marker on a type that is not an
  integer narrower than 32 bits.
- Frontends set the markers to match the C ABI.

## Alternatives

- **Markers required on every narrow parameter.** Noisy for every caller
  that is not C, which has no use for them.

## Consequences

- funk can call C, including `printf`.
- The x86-64 backend extends a marked argument at the call and a marked
  result at the return, and nothing unmarked. An `i1` marked `zext` is a C
  `_Bool`.
