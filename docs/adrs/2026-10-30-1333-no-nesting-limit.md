# fir has no nesting limit, and funk-ir walks nested IR with explicit stacks

Status: accepted

## Context

Attributes (`h(h(x))`), regions (an op's region holds blocks of ops that
own regions) and items (a body of items) nest in fir text and IR. The spec
limits numbers (N3), but not nesting.

`funk-ir` (#9) parsed, printed, verified, compared and dropped them
recursively, one native stack frame or more per level. The `funk` binary
ran on a 1 GiB reserved stack, and a text nested 3 million levels deep still
aborted it with a stack overflow and no verdict, which breaks
ADR-2026-10-30-1032. A library caller on a 2 to 8 MB thread failed after a
few thousand levels.

The human ruled on 2026-10-30 (#36): fir has no nesting limit. "There's no
point in introducing a random nesting limit." Every tool must handle any
depth.

`unsafe_code` is forbidden and `funk-ir` takes no third-party crates
(ADR-2026-10-30-1030), so a crate that grows the stack, such as `stacker`,
is out.

## Decision

- **No limit.** Every text the grammar accepts parses at any depth, and the
  IR holds any depth. Nothing in `funk-ir` recurses once per level of
  nesting: each level costs constant native stack, and the path from the
  root lives in a `Vec` on the heap.
- **One module of tree helpers**, `ir/tree.rs`. `walk` gives the `Enter` and
  `Leave` steps of a depth-first walk over any `Node`; `equal` and `hash`
  compare and hash trees from walks; `Nest` builds a tree top down, with the
  lists that enclose the one being built on a stack and each element put
  where it ends up; `drop_all` frees a tree one node at a time.
- **Hand-written traits only where nesting turns.** `Attr` and `Region`
  write `Clone`, `PartialEq`, `Eq`, `Hash`, `Debug` and `Drop` with these
  helpers. `Type`, `Block`, `Op`, `Func`, `Item` and `Module` keep their
  derives, which reach the hand-written ones within one level. `Debug`
  writes, byte for byte, what `#[derive(Debug)]` writes, `{:#?}` included; a
  test checks it against a derived copy of the types.
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
  thread is gone. This replaces the last consequence of ADR-2026-10-30-1032.
- **Tests on small stacks.** On threads of 256 KiB, `tests/deep.rs` of
  `funk-ir` parses, prints, verifies, clones, compares, hashes, debug-formats
  and drops ten million levels of attributes; parses, verifies, hashes,
  debug-formats and drops ten million levels of regions; and parses and
  drops ten million levels of items. Regions are cloned and compared one
  million levels deep, and printed 3,000 deep. `funk verify` and `funk fmt`
  give their verdicts on ten-million-level files with a 1 MiB stack.

## Alternatives

- **A nesting limit in the spec**, like N3: a change to the text format,
  which the ruling rejects.
- **A limit in the implementation, reported as a resource error**: `funk`
  and `fir-ref` would disagree on deep texts.
- **Growing the stack**, with a crate or a new thread every N levels: needs
  a crate or `unsafe`, and derived traits give no place to hook it.

## Consequences

- **Public API.** `Attr` and `Region` implement `Drop`, so code cannot move
  a field out of an owned `Attr` or `Region` (E0509): it borrows, clones, or
  takes the field with `std::mem::take`. The rest of the API is unchanged.
- Code that walks attributes or regions uses `walk` or `Region::parts`. A
  walk over them that recurses is a bug.
- Memory bounds depth, not the stack. A level of regions takes about 340
  bytes of IR, so ten million levels take 3.3 GB; that is why the tests that
  hold two copies of nested regions run a million levels deep.
- Each level of regions indents its blocks and ops further, so the
  canonical text of nested regions grows with the square of their depth,
  and so does `{:#?}`. Printing them is bounded by the size of what it
  writes, not by the stack.
- The Lean side, `fir-ref` and #10's parser and printer, follows the same
  rule; #10 tracks it.
