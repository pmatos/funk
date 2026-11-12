# Test cases ported from LLVM live in tests/fir/llvm/ beside LLVM's licence, and each names its source

Status: accepted
Tier: direction; area: testing-and-harness

## Decision

- **A directory of its own.** Ported cases live in `tests/fir/llvm/`, each a
  canonical, valid module `NAME.fir` and its sidecar `NAME.toml`.
- **The licence and a notice beside them.**
  [`tests/fir/llvm/LICENSE.TXT`](../../tests/fir/llvm/LICENSE.TXT) is
  `llvm/LICENSE.TXT` of the pinned commit.
  [`tests/fir/llvm/README.md`](../../tests/fir/llvm/README.md) is the notice:
  the files derive from LLVM under that licence, not funk's, were changed by
  translation into fir by hand, and each module's source is listed.
- **Provenance as data.** A ported sidecar has `source = { file, commit }`,
  and each test has `from`, the LLVM function or CHECK lines it is. Each
  function's ops carry a location, a source range of the LLVM test file.
- **One commit.** Every module names llvm-project
  `7a941dfb2877a0b8cf30323fefa85ad019e0b0f5` (`llvmorg-23.1.4`). Moving to
  another means moving every module, or editing this ADR to allow several.
- **The harness checks it**: the licence and notice are present, the licence's
  SHA-256, a sidecar for each module with a well-formed `source`, `from` on
  each test, no other file, and one commit. Outside `llvm/`, `source` and
  `from` are unknown keys.
- **No LLVM files in the repository.** Only the hand translations come in.

## Why

LLVM is under the Apache License v2.0 with LLVM Exceptions, and funk under MIT.
A ported case derives from an LLVM test file, so its recipients need the
licence and a notice that the files were changed. A canonical `.fir` text holds
no comments, so the provenance cannot ride in the text; as data, the harness
can check it.

## Rejected alternatives

- **`canonical/llvm-*.fir` with provenance in comments only.** The licence
  would not sit beside the files it covers, and nothing would check a source.
- **Copying the `.ll` files in.** No tool of funk reads LLVM IR.
