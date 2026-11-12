# A module declares its memories in a data layout line after its dialect set

Status: accepted
Tier: direction; area: text-format

## Decision

- **Spelling.** After the dialect set, a module's text may hold the word
  `layout`, then one entry per memory, separated by `, `, then an empty
  line. An entry is `memory(N, unit(U), pointer(P), O)`, then `align(A)`
  when given and `nonintegral` when set, in that order:
  `layout memory(1, unit(16), pointer(32), little, align(4), nonintegral)`.
  `O` is `little` or `big`. Every other attribute, and any number above
  16,777,215, does not decode. Entries keep the text's order.
- **Default.** A module with no line has the empty layout: memory 0 alone,
  with 8-bit units, 64-bit little-endian pointers of natural alignment,
  integral. A layout that leaves memory 0 out gives it this entry. So every
  earlier text is unchanged.
- **Meaning.** `U` and `P` are bits. `A` is the alignment of the memory's
  pointers in units; without it, the least power of two at least
  `ceil(P / U)`. `nonintegral` is LLVM's `ni:`: #232 rejects `ptr.expose`
  and `ptr.from_int` on such a memory.
- **Validity.** An entry is valid when `U` and `P` are at least 1, `A` is a
  power of two, and `O` is `little`. Each memory is declared once. Every
  pointer type that the module states names memory 0 or a declared memory:
  `ptr(N)` is valid exactly when the layout declares `N`.
- **One layout.** The layout is the top-level module's. A nested module
  writes none, and its types name its parent's memories.

The human ruled on 2026-11-11 on #231, as the orchestrator recorded: M1
admits only `little`, so validation rejects a `big` memory, and the layout
carries a per-memory non-integral flag.

## Why

ADR-2026-11-09-1542 has the data layout give each memory its unit and
pointer width, and leaves the spelling open. A line after the dialect set,
in the style of ADR-2026-11-10-1306, keeps every M0 text, and its entries
are attributes, so no lexer change.

## Rejected alternatives

- **LLVM's string, `"e-p1:32:32-ni:1"`.** One opaque string with a second
  grammar inside it, which both parsers and the round-trip proofs would
  have to read.
- **Positional entries, `memory(1, 16, 32)`.** Shorter, but a reader cannot
  tell the unit from the pointer width.
- **A layout per nested module.** No dialect needs one in M1, and memory
  numbers shared across a host and its device modules are simpler; a
  dialect that needs its own can revisit this.
