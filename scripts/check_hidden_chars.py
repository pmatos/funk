"""Fail when a text file passed by pre-commit holds a raw invisible control.

Bidirectional controls, directional marks, the byte-order mark and the line
and paragraph separators can make text show an order of characters other
than the one a tool reads (the Trojan Source attack). Write them as escapes.
"""

import sys

HIDDEN = {
    **{cp: "bidirectional control" for cp in range(0x202A, 0x202F)},
    **{cp: "bidirectional isolate" for cp in range(0x2066, 0x206A)},
    0x200E: "left-to-right mark",
    0x200F: "right-to-left mark",
    0x061C: "Arabic letter mark",
    0xFEFF: "byte-order mark",
    0x2028: "line separator",
    0x2029: "paragraph separator",
}


def hidden_chars(path: str) -> list[tuple[int, int, int]]:
    """Return (line, column, code point) for each hidden character in a file."""
    with open(path, encoding="utf-8", errors="replace", newline="") as f:
        text = f.read()
    found = []
    for line_no, line in enumerate(text.split("\n"), start=1):
        for col, ch in enumerate(line, start=1):
            if ord(ch) in HIDDEN:
                found.append((line_no, col, ord(ch)))
    return found


def main(paths: list[str]) -> int:
    failed = False
    for path in paths:
        for line_no, col, cp in hidden_chars(path):
            failed = True
            print(
                f"{path}:{line_no}:{col}: raw U+{cp:04X} ({HIDDEN[cp]})",
                file=sys.stderr,
            )
    if failed:
        print(
            "\nWrite these characters as escapes, such as \\u202e in Lean or"
            " \\u{202e} in fir text.",
            file=sys.stderr,
        )
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
