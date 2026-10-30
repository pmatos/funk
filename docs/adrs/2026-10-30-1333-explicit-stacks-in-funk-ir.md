# funk-ir walks nested IR with explicit stacks

Status: accepted

## Context

fir has no nesting limit (ADR-2026-10-30-1549): every tool handles
attributes, regions and items nested to any depth, without a stack
overflow and without a large stack.

`funk-ir` (#9) parsed, printed, verified, compared and dropped them
recursively, one native stack frame or more per level. The `funk` binary
ran on a 1 GiB reserved stack, which held about a million levels.

`unsafe_code` is forbidden and `funk-ir` takes no third-party crates
(ADR-2026-10-30-1030), so a crate that grows the stack, such as `stacker`,
is out.

## Decision

- **No recursion per level.** Nothing in `funk-ir` recurses once per level
  of nesting: each level costs constant native stack, and the path from
  the root lives in a `Vec` on the heap.
- **One module of tree helpers**, `ir/tree.rs`. `walk` gives the `Enter` and
  `Leave` steps of a depth-first walk over any `Node`; `equal` and `hash`
  compare and hash trees from walks; `Nest` builds a tree top down, with the
  lists that enclose the one being built on a stack and each element put
  where it ends up; `drop_all` frees a tree one node at a time.
- **Hand-written traits only where nesting turns.** `Attr` and `Region`
  write `Clone`, `PartialEq`, `Eq`, `Hash`, `Debug` and `Drop` with these
  helpers. `Type`, `Block`, `Op`, `Func`, `Item` and `Module` keep their
  derives, which reach the hand-written ones within one level. `Debug`
  writes, byte for byte, what `#[derive(Debug)]` writes, in every form:
  `{:?}`, `{:#?}`, `{:x?}`, `{:#x?}` and with widths. A test checks it
  against a derived copy of the types. In the `{:#?}` form, a value that
  can span lines goes through an indenting writer, which keeps only the
  alternate flag; such values hold no numbers, so no flag changes them. The
  one number, an op's `LocRef`, gets the caller's formatter and all its
  flags.
- **Walks over parts.** A `Part` is a region, a block or an op. The printer,
  the decoder and the traits of `Region` walk parts.
- **The parser.** The lexer gives one token at a time, so no list of tokens
  takes memory. Items, regions and the arguments of attributes are read
  into a `Nest`. Blocks and ops are read straight into the IR, and the text
  positions that decoding reports are kept beside them in the order of the
  text, which is the order of a depth-first walk. The order of errors of
  ADR-2026-10-30-1032 holds: when the grammar fails, the rest of the text is
  still read, and an error in its characters or tokens wins.
- **No large stack in `funk`.** It runs on its main thread; the 1 GiB worker
  thread is gone. As before, a panic exits with status 2. This replaces the
  last consequence of ADR-2026-10-30-1032.
- **Tests on small stacks.** On threads of 256 KiB, `tests/deep.rs` of
  `funk-ir` parses, verifies, clones, compares, hashes, debug-formats and
  drops a million levels of attributes and of regions, prints the
  attributes, and parses and drops a million levels of items. Regions are
  printed 3,000 levels deep, which already overflows a printer that
  recurses. `funk verify` and `funk fmt` give their verdicts on files a
  million levels deep with a 1 MiB stack.

## Alternatives

- **Growing the stack**, with a crate or a new thread every N levels: needs
  a crate or `unsafe`, and derived traits give no place to hook it.
- **A large reserved stack**, as `funk` had: it moves the overflow deeper
  but keeps it, and a library caller does not get it.

## Consequences

- **Public API.** `Attr` and `Region` implement `Drop`, so code cannot move
  a field out of an owned `Attr` or `Region` (E0509): it borrows, clones, or
  takes the field with `std::mem::take`. The rest of the API is unchanged.
- Code in `funk-ir` that walks attributes or regions uses `walk` or
  `Region::parts`, which are `pub(crate)`. Other crates walk the public
  `blocks`, `ops`, `regions` and `Attr::App` arguments with an explicit
  stack of their own. A walk that recurses once per level is a bug
  anywhere.
- Memory bounds depth, not the stack.
- Each level of regions indents its blocks and ops further, so the
  canonical text of nested regions grows with the square of their depth,
  and so does `{:#?}`. Printing them is bounded by the size of what it
  writes, not by the stack. `funk fmt` holds the whole canonical text in
  memory, even for `--check`, so a small text that is not canonical can
  exhaust memory; #51 tracks streaming it.
