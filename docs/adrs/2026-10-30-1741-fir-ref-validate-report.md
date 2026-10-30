# `fir-ref validate` reports in the JSON schema of `funk verify --json`

Status: accepted

## Context

[#10](https://github.com/pmatos/funk/issues/10) asks for
`fir-ref validate`, which prints a JSON verdict on a file: accepted,
rejected by the parser with the reason and the position, or rejected by
validation with the reasons. The harness of
[#13](https://github.com/pmatos/funk/issues/13) compares it with
`funk verify --json`, whose report ADR-2026-10-30-1032 fixes, and compares
verdicts, never messages. `fir-ref`'s command line follows `funk`'s
(ADR-2026-10-30-1425).

## Decision

- **Command.** `fir-ref validate FILE...` parses each file with the core
  dialect and runs the spec's validation check, `Module.problems`. A FILE
  of `-` is standard input, at most once, and `--` ends the options. It has
  no options: its output is always JSON.
- **Report.** One JSON object per file, on one line of standard output, in
  the order of the files: `{"file": ..., "verdict": ..., "diagnostics":
  [...]}`, exactly as `funk verify --json` writes it.
  - `verdict` is `accepted`, `parse-error`, `validation-error` or
    `io-error`.
  - A diagnostic has a `kind` (`parse-error`, `validation-error` or
    `io-error`) and a `message`. A parse error adds `line` and `column`
    (UTF-8 bytes from 1); the parser reports its first error only. A
    validation error adds `func`, `block`, `op` (the op's index in its
    block) and `loc`, `{"ref": N, "location": "..."}` with the location as
    the table prints it, or `null` when the table lacks the reference; each
    is `null` when it does not apply. There is one validation error for
    each problem that the check finds, in the check's order.
  - Strings escape `"`, `\`, the line feed, the tab and the carriage
    return, and every other character that a fir string escapes as
    `\uXXXX` in UTF-16, as `funk` does.
- **Exit status.** 0 when every file is accepted, 1 when one is rejected by
  the parser or by validation, 2 on a usage or I/O error, the largest over
  the files. A file that cannot be read still gets its report, with the
  verdict `io-error`.

## Alternatives

- **A schema of its own**, such as `{"verdict": "rejected-by-parser"}`.
  #13 would translate one tool's output before comparing.
- **`--json`, as `funk verify` has.** `fir-ref validate` exists for tools
  and has no text output to choose from.

## Consequences

- #13 compares `verdict` field by field with `funk verify --json`, with no
  translation, and on a text with one parse error, `line` and `column` too.
- Messages, and the `func`, `block`, `op` and `loc` fields, are for people:
  the two tools may word or place a problem differently.
- A change to `funk`'s report schema needs the same change here, and a new
  ADR.
