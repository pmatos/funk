# funk fmt streams the canonical text and never holds it whole

Status: accepted
Tier: implementation; area: rust-ir-and-tools

## Context

The canonical text of nested regions grows with the square of their depth
(ADR-2026-10-30-1333). `funk fmt` built the whole text of a module in one
`String`, even for `--check`, which needs only a yes or no. A 300 KB file
of 20,000 nested regions with no indentation has a canonical text of
2.4 GB: `funk fmt --check` took 2.3 GiB, and under a smaller memory limit
it aborted with no verdict, where ADR-2026-10-30-1032 promises one
([#51](https://github.com/pmatos/funk/issues/51)).

## Decision

- **The printer writes to a sink.** `funk_ir::text::write_module` writes a
  module's canonical text to any `fmt::Write`, piece by piece, and stops at
  the sink's first error. `print`, `print_op` and `print_func` are thin
  wrappers that return a `String`. The printed bytes do not change.
- **`--check` compares as it prints.** The sink holds the bytes of the file
  that the text has not reached yet, and fails at the first piece that
  differs. The file is canonical when the printer finishes and no byte is
  left.
- **`--write` streams into its temporary file**, through a buffer. It
  first checks the file as `--check` does, so a canonical file is left
  alone and no temporary file appears.
- **Plain `fmt` streams to standard output**, through a buffer.
- **`fmt --json` streams the escaped text** as the report's last field,
  `text`. The report gives `canonical` before `text`, so funk checks the
  file first, then prints the text a second time.

## Consequences

- `funk fmt --check` and `--write` hold the file and its module, never the
  canonical text: memory is linear in the input. On the file above,
  `--check` takes 12 MiB, and `crates/funk/tests/fmt_check_memory.rs` gets
  its verdict with 256 MiB of data.
- Plain `fmt` and `fmt --json` still write the whole text, so their time
  and output grow with it, but not their memory.
- `fmt --json` prints every text twice, and `--write` prints twice the
  text of a file that is not canonical; the first pass stops at the first
  difference. `fmt --json` on a canonical file costs one full pass more
  than before.
