# In a sum, a base op sees only the context that its base can write

Status: accepted; refined by ADR-2026-11-10-1310
Tier: direction; area: validation

## Decision

In the spec's sum `base ⊞ e` (ADR-2026-11-09-2306), an op of the base is
checked by the base's rule, `validOp`, in an `OpContext base`. The context's
symbol table and result types are stated in the sum's types, which the base
cannot always write.

- **Symbols.** A base op sees the symbols whose parameter and result types
  are all the base's. Any other symbol looks undefined to it, so a core
  `call` of a function that takes an extension's type is invalid.
- **Result types.** A base op sees the function's result types only when
  they are all the base's (`Dialect.sum.baseContext`). Otherwise no base op
  is valid in that function (`Dialect.sum.BaseValidOp`), not even `add`.
- **The extension** sees the whole context, since its types are the sum's.

The human ruled on 2026-11-10 on #227 to merge this as is: the strict rule
stands and may be relaxed later, and the core's control ops are not made
generic now.

## Why

The base has no word for an extension's types, so the sum decides what a
base op sees. This rule is decidable for every dialect and lets no base op
judge a context it cannot read. It is stricter than needed, since only the
core's `ret` reads the result types; lifting that limit, and letting a core
`br`, `ret` or `call` pass a value of an extension's type, needs the core's
control ops to be generic in their types.

## Rejected alternatives

- **Drop the result types that the base cannot write.** A core `ret` with
  fewer values than the function declares would then be valid, and no rule
  would catch it.
- **Judge a base op whatever the result types are.** "Valid for every list
  of result types" cannot be decided for every dialect, and the validation
  check must decide it (ADR-2026-11-09-2257).
- **Ask each dialect whether its op reads the result types.** A new member
  of `DialectValidation`, and a change to every dialect, for one case.
