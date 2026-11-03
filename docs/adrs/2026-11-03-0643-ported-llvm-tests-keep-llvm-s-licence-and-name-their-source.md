# Test cases ported from LLVM live in tests/fir/llvm/ beside LLVM's licence, and each names its source

Status: accepted

## Context

[#23](https://github.com/pmatos/funk/issues/23) asks for LLVM test cases
ported to fir by hand, each with its source and licence noted. LLVM is
under the Apache License v2.0 with LLVM Exceptions; funk is under the MIT
licence. A ported case is a work derived from an LLVM test file, so the
licence asks for three things: a copy of the licence for its recipients,
a notice that the files were changed, and any copyright notice of the
source kept. LLVM's test files carry no copyright notice of their own;
`llvm/LICENSE.TXT` holds the project's, and llvm-project has no `NOTICE`
file.

The corpus (ADR-2026-10-30-2050) has no place for a licence file, and a
canonical `.fir` text holds no comments, so a ported module cannot carry
a notice as a comment.

## Decision

- **A directory of its own.** The ported cases live in `tests/fir/llvm/`:
  `NAME.fir`, a canonical, valid module, and its sidecar `NAME.toml`,
  which every ported module has. `NAME` is the LLVM directory
  (`instsimplify`, `instcombine`, or `x86` for `CodeGen/X86`) and the
  stem of the test file, with a suffix where one file is split between
  modules, by width or by size.
- **The licence and a notice beside them.**
  [`tests/fir/llvm/LICENSE.TXT`](../../tests/fir/llvm/LICENSE.TXT) is
  `llvm/LICENSE.TXT` of the pinned commit, but for the empty line that
  ends that file, which the `end-of-file-fixer` hook removes.
  [`tests/fir/llvm/README.md`](../../tests/fir/llvm/README.md) is the
  notice: the files are derived from LLVM, at that commit, under that
  licence, not funk's; they were changed, by translation into fir by
  hand; and it lists each module with its source.
- **Provenance as data.** A ported sidecar has
  `source = { file = "...", commit = "..." }`: the LLVM test's path in
  llvm-project and the full hash of the commit it was read at. Each of
  its tests has `from`: the LLVM function, or its CHECK lines, or the
  file's RUN line, that the test's function is. Each sidecar's comment
  starts "Derived from LLVM" and says how its cases were rewritten.
- **The texts mark themselves.** Each function's ops carry one location,
  a source range of the LLVM test file: the function's lines, or the
  CHECK lines that its folded form comes from.
- **One commit.** Every module names llvm-project
  `7a941dfb2877a0b8cf30323fefa85ad019e0b0f5`, the tag `llvmorg-23.1.4`.
- **The harness checks it.** `scripts/harness/corpus.py` reports a
  missing `LICENSE.TXT` or `README.md`, a module without a sidecar, a
  sidecar without a well-formed `source`, a test without `from`, any
  other file in the directory, and modules from more than one commit.
  Outside `llvm/`, `source` and `from` are unknown keys.
- **Every reader reads it.** The modules are canonical texts like those
  of `canonical/`: `crates/funk-ir/tests/corpus.rs` round-trips and
  validates them, the `fir_texts` example prints them for the
  cross-language round trip, `scripts/check-fir-ref.sh` reprints and
  validates them, and the differential harness runs their tests.
- **No LLVM files in the repository.** Only the hand translations come
  in. The LLVM files they were made from are read from GitHub at the
  pinned commit and stay out.

## Alternatives

- **`canonical/llvm-*.fir`, with provenance in comments only.** No
  change to the corpus's readers, but the licence would not sit beside
  the files it covers, and nothing would check a source or a commit.
- **Copying the `.ll` files in.** They would bring LLVM's text without a
  use, as no tool of funk reads LLVM IR.

## Consequences

- Porting another case means adding a module and its sidecar here, with
  `source` and `from`; the harness rejects one without them.
- Porting from a newer llvm-project commit means moving every module to
  it, or a new ADR that allows several commits.
- The corpus has a fifth place, and ADR-2026-10-30-2050's "nothing else
  but README.md" now reads with `llvm/` added.
