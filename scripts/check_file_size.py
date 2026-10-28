"""Fail when a text file passed by pre-commit exceeds the file-size budget."""

import os
import sys

MAX_BYTES = 20_000


def main(paths: list[str]) -> int:
    sizes = ((path, os.path.getsize(path)) for path in paths)
    over = [(path, size) for path, size in sizes if size > MAX_BYTES]
    if not over:
        return 0
    print(
        f"Files over the {MAX_BYTES:,}-byte budget (ADR-2026-10-28-0724):",
        file=sys.stderr,
    )
    for path, size in over:
        print(f"  {path}: {size:,} bytes", file=sys.stderr)
    print(
        "\nSplit each file by responsibility so every part is at or below the"
        " budget:\n"
        "  1. Group related functions, types, tests or doc sections.\n"
        "  2. Move each cohesive group into a focused sibling file or module.\n"
        "  3. Keep a small entry point; update imports, links and callers.\n"
        "  4. Re-run the checks, git add every new and changed file, commit.\n"
        "Do not minify, cram or shorten names to fit. Only generated or vendored"
        " files may be\nexcluded, via this hook's exclude in .pre-commit-config.yaml.",
        file=sys.stderr,
    )
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
