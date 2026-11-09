# In a sum, a base op sees only the context that its base can write

Status: accepted
Tier: direction; area: validation

## Context

In the spec's sum `base ⊞ e` (ADR-2026-11-09-2306), an op of the base is
checked by the base's rule, `validOp`, in an `OpContext base`. That context
holds the module's symbol table and the result types of the function that
holds the op. In the sum both are stated in the sum's types, which hold
`e`'s own types too. The base has no word for those, so the sum must decide
what a base op sees when the context names them.

## Decision

- **Symbols.** A base op sees the symbols whose parameter and result types
  are all the base's. Any other symbol looks undefined to it, so a core
  `call` of a function that takes an extension's type is invalid.
- **Result types.** A base op sees the function's result types only when
  they are all the base's (`Dialect.sum.baseContext`). Otherwise no base op
  is valid in that function (`Dialect.sum.BaseValidOp`).
- **The extension** sees the whole context, since its types are the sum's.

## Alternatives

- **Drop the result types that the base cannot write.** A core `ret` with
  fewer values than the function declares would then be valid, and no rule
  would catch it.
- **Judge a base op whatever the result types are.** "Valid for every list
  of result types" cannot be decided for every dialect, and the validation
  check must decide it (ADR-2026-10-30-1740).
- **Ask each dialect whether its op reads the result types.** That needs a
  new member of `DialectValidation`, and a change to every dialect, for one
  case.

## Consequences

- No core op, not even `add`, is valid in a function that returns a value of
  an extension's own type. Such a function needs the extension's own ops
  throughout. Only the core's `ret` reads the result types, so this is
  stricter than it needs to be.
- The core's ops carry core types only. So a core `br`, `ret` or `call`
  cannot pass a value of an extension's own type either (ADR-2026-11-09-2306).
  Lifting both limits needs the core's control ops to be generic in their
  types. #227 does not cover that.
