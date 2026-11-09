"""Compares funk's instruction counts with the committed baseline (#174).

Usage: python3 -I scripts/rust_speed.py sizes BASELINE
       python3 -I scripts/rust_speed.py compare BASELINE MEASURED [--advisory]

sizes prints the input sizes that BASELINE was measured at: adds and blocks.
compare reads MEASURED, one "input command count" per line, prints every
count against the baseline, and exits with 1 when any count is more than
MARGIN_PERCENT above it. With --advisory it prints the same report and exits
with 0: only CI is authoritative. It exits with 2 on a malformed file.
"""

import json
import sys

COMMANDS = ("fmt", "verify", "build")
INPUTS = ("adds", "blocks")
MARGIN_PERCENT = 10


class BadFile(Exception):
    """A baseline or a measurement that does not hold what it must."""


def is_count(value) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value > 0


def require_keys(path: str, label: str, value, keys: tuple[str, ...]) -> None:
    if not isinstance(value, dict) or sorted(value) != sorted(keys):
        raise BadFile(f"{path}: {label} must name exactly {', '.join(keys)}")


def load_baseline(path: str) -> dict:
    with open(path, encoding="utf-8") as file:
        data = json.load(file)
    if not isinstance(data, dict):
        raise BadFile(f"{path}: expected a JSON object")
    for key in ("recorded_on", "glibc", "valgrind"):
        if not isinstance(data.get(key), str):
            raise BadFile(f"{path}: {key} must be a string")
    sizes = data.get("sizes")
    require_keys(path, "sizes", sizes, INPUTS)
    if not all(is_count(size) for size in sizes.values()):
        raise BadFile(f"{path}: every size must be a positive integer")
    counts = data.get("instructions")
    require_keys(path, "instructions", counts, INPUTS)
    for input_name, row in counts.items():
        require_keys(path, input_name, row, COMMANDS)
        if not all(is_count(count) for count in row.values()):
            raise BadFile(
                f"{path}: every count of {input_name} must be a positive integer"
            )
    return data


def parse_measured(text: str) -> dict[tuple[str, str], int]:
    measured: dict[tuple[str, str], int] = {}
    for line in text.splitlines():
        fields = line.split()
        if len(fields) != 3 or not fields[2].isdecimal() or int(fields[2]) == 0:
            raise BadFile(f"malformed measurement: {line!r}")
        input_name, command, count = fields
        if (input_name, command) in measured:
            raise BadFile(f"measured twice: {input_name} {command}")
        measured[input_name, command] = int(count)
    expected = {(i, c) for i in INPUTS for c in COMMANDS}
    if set(measured) != expected:
        difference = sorted(set(measured) ^ expected)
        raise BadFile(
            f"measurements do not match the inputs and commands: {difference}"
        )
    return measured


def over_margin(old: int, new: int) -> bool:
    return new * 100 > old * (100 + MARGIN_PERCENT)


def percent_change(old: int, new: int) -> float:
    return (new - old) * 100 / old


def report(
    baseline: dict, measured: dict[tuple[str, str], int]
) -> tuple[list[str], list[str]]:
    """Returns the lines of the table and one line per count over the margin."""
    table = [f"{'input':<8}{'command':<9}{'baseline':>15}{'measured':>15}{'change':>9}"]
    over = []
    for input_name in INPUTS:
        for command in COMMANDS:
            old = baseline["instructions"][input_name][command]
            new = measured[input_name, command]
            percent = percent_change(old, new)
            table.append(
                f"{input_name:<8}{command:<9}{old:>15}{new:>15}{percent:>+8.2f}%"
            )
            if over_margin(old, new):
                over.append(
                    f"funk {command} on {input_name}: {old} -> {new} ({percent:+.2f}%)"
                )
    return table, over


def compare(baseline_path: str, measured_path: str, advisory: bool) -> int:
    baseline = load_baseline(baseline_path)
    with open(measured_path, encoding="utf-8") as file:
        measured = parse_measured(file.read())
    print(
        f"Baseline: {baseline['recorded_on']}, {baseline['glibc']}, {baseline['valgrind']}. "
        f"Margin: {MARGIN_PERCENT}%."
    )
    table, over = report(baseline, measured)
    print("\n".join(table))
    if not over:
        print("Every count is within the margin of the baseline.")
        return 0
    print(f"More than {MARGIN_PERCENT}% above the baseline:")
    print("\n".join(over))
    if advisory:
        print("Advisory only: counts on another host differ. CI decides.")
        return 0
    print(
        "Fix the slowdown, or raise the baseline and give the old and new numbers in the PR."
    )
    print(
        "If this host's glibc or valgrind differs from the baseline's, the runner may have moved the counts."
    )
    return 1


def main(argv: list[str]) -> int:
    try:
        if len(argv) == 2 and argv[0] == "sizes":
            sizes = load_baseline(argv[1])["sizes"]
            print(*(sizes[name] for name in INPUTS))
            return 0
        if argv[:1] == ["compare"] and (
            len(argv) == 3 or (len(argv) == 4 and argv[3] == "--advisory")
        ):
            return compare(argv[1], argv[2], len(argv) == 4)
    except (BadFile, OSError, json.JSONDecodeError) as error:
        print(f"rust_speed: {error}", file=sys.stderr)
        return 2
    print(__doc__.split("\n\n")[1], file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
