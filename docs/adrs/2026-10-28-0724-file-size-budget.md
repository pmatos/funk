# Authored text files are at most 20,000 bytes

Status: accepted
Tier: direction; area: process

## Decision

- Every text file in the repository is at most 20,000 bytes: about 5k tokens
  of prose, 5–7k tokens of code.
- The `file-size-budget` pre-commit hook (`scripts/check_file_size.py`)
  enforces it. On commit, pre-commit passes it the staged text files and skips
  binaries. CI runs it over every file, as a step of the `static` job
  (ADR-2026-11-05-1408).
- The cap is strict for every file. There is no ratchet that lets an
  oversized file stay.
- Only generated or vendored files are exempt, through the hook's `exclude`
  pattern in `.pre-commit-config.yaml`. Authored code is never exempt.
- Modules are split by responsibility from the start. When the hook fails, it
  names each file and its size and says how to split.

The human set this rule on 2026-10-28, in #2, which adopted it from jsse.

## Why

Agents develop funk. An agent works best on a file it can read whole: it sees
every definition at once and spends little context doing so. Large files get
read in fragments, and edits then miss code the agent never saw. jsse enforces
the same cap, and the practice has paid off there.

## Rejected alternatives

- **Count real tokens.** Claude's tokenizer is not available offline. Proxies
  such as tiktoken download data inside a commit hook and still do not give
  Claude's count. Bytes are deterministic, instant and language-neutral, and
  the cap is a budget, so the exact count does not matter.
- **Port jsse's checker.** It reads blobs with git plumbing, ratchets
  oversized files and has a separate diff-based CI mode. pre-commit already
  gives staged content, file selection and binary detection, so funk's checker
  is a few lines, and local and CI runs are the same.
