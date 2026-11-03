"""Reads what `cargo verus verify -- --output-json` printed, for
scripts/check-verus.sh (ADR-2026-11-03-0808, ADR-2026-11-03-0809).

Each crate that opts into Verus must have verified, with no error, each
function of REQUIRED: those whose proofs that ADR relies on. Verus lists
every function that it saw in a report's `func-details`. A cfg that hides
a verified module from Verus, but not from cargo, leaves its functions out,
even when Verus verifies some other item of the crate.

Usage: python3 -I scripts/verus_report.py RESULTS.json CRATE...
"""

import json
import sys

# Crate -> the functions, by their path in the crate, that Verus must verify.
REQUIRED = {
    "funk-start-fds": ("record::record", "record::record_slots"),
}


def reports(text: str) -> list[dict]:
    """Verus prints one JSON object for each crate that it verifies."""
    decoder, at, found = json.JSONDecoder(), 0, []
    while True:
        at = len(text) - len(text[at:].lstrip())
        if at == len(text):
            return found
        report, at = decoder.raw_decode(text, at)
        found.append(report)


def report_of(crate: str, all_reports: list[dict]) -> dict | None:
    prefix = crate.replace("-", "_") + "::"
    mine = [
        r for r in all_reports if any(f.startswith(prefix) for f in r["func-details"])
    ]
    return mine[-1] if mine else None


def crate_problems(crate: str, all_reports: list[dict]) -> list[str]:
    prefix = crate.replace("-", "_") + "::"
    report = report_of(crate, all_reports)
    if report is None:
        return [f"Verus verified nothing in {crate}"]
    results, details = report["verification-results"], report["func-details"]
    found = []
    if not results.get("success") or results.get("errors") != 0:
        found.append(f"Verus failed in {crate}: {results}")
    required = REQUIRED.get(crate)
    if not required:
        found.append(
            f"{crate} opts into Verus, but scripts/verus_report.py names no"
            " function that Verus must verify in it"
        )
    for name in (prefix + f for f in required or ()):
        if name not in details:
            found.append(
                f"Verus did not see {name}: a cfg may hide its module from Verus"
            )
        elif details[name].get("failed_proof_notes"):
            found.append(f"Verus did not prove {name}: {details[name]}")
    return found


def problems(text: str, crates: list[str]) -> list[str]:
    all_reports = reports(text)
    return [p for crate in crates for p in crate_problems(crate, all_reports)]


def main(argv: list[str]) -> int:
    with open(argv[1], encoding="utf-8") as f:
        text = f.read()
    found = problems(text, argv[2:])
    for message in found:
        print(message, file=sys.stderr)
    if found:
        return 1
    all_reports = reports(text)
    for crate in argv[2:]:
        count = report_of(crate, all_reports)["verification-results"]["verified"]
        names = ", ".join(REQUIRED[crate])
        print(f"{crate}: Verus verified {count} items, among them {names}; 0 errors")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
