# `fir-ref`'s command line follows `funk`'s

Status: accepted

## Context

`fir-ref` is the reference interpreter's executable (ADR-2026-10-29-2009).
The harness of [#13](https://github.com/pmatos/funk/issues/13) runs it and
`funk` on the same texts. It compares their verdicts, and the position of
a parse error in a text with one error, never their wording, as
ADR-2026-10-30-1032 says of `funk`'s reports.
[#10](https://github.com/pmatos/funk/issues/10) gives `fir-ref` three
commands: `fmt`, then `validate` and `run`, whose JSON output it specifies.

## Decision

- **Commands.** `fir-ref COMMAND ...`. The first command is
  `fmt [--check] FILE...`: it parses each file with the core dialect and
  prints it in canonical form with the spec's printer, `Module.print`, as
  `funk fmt` does. `--check` prints the name of each file that is not
  canonical instead. A FILE of `-` is standard input, and `--` ends the
  options. `validate` and `run` follow.
- **Exit status.** The status of ADR-2026-10-30-1032: 0 when every file is
  accepted, and canonical under `--check`; 1 when one is rejected, or not
  canonical under `--check`; 2 on a usage or I/O error.
- **Parse errors.** A parse error is one line on standard error,
  `FILE:LINE:COL: parse error: REASON`, as `funk` writes it. Bytes that are
  not UTF-8 are a parse error at the first byte of the first sequence that
  is not well formed, as in `funk`.

## Alternatives

- **A format of its own.** #13 would translate each tool's output before
  comparing them.
- **`--write` and `--json` for `fmt`, as `funk` has.** `fir-ref fmt` exists
  so that #13 can compare printed texts; it rewrites no files, and its
  verdict is its exit status.

## Consequences

- #13 reads the verdicts of `funk` and `fir-ref` from their exit status,
  and the position of a parse error from `LINE:COL`, with no translation.
- #13 uses `fir-ref fmt` to check that both sides print each non-canonical
  text of `tests/fir/` as its canonical sibling.
- A change to `funk`'s exit status or to its parse-error line needs the same
  change in `fir-ref`.
