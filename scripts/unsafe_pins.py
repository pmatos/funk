"""The pinned text of the trusted base and of #117's specification, for
scripts/check_unsafe_code.py (ADR-2026-11-03-0808).

Verus assumes a trusted item's specification without proof, and proves
`record` against the specification that `recorded`, `finish` and
`record_slots`' signature state. An edit to any of them changes what the
proof means, and Verus would still pass. So each is pinned by a digest of
its tokens: its text without comments or layout, with its attributes and
the contents of its string literals. All the text outside `verus!` is
pinned too. What may change without a new pin is `record_slots`' body,
which Verus proves against its pinned signature, and new items inside
`verus!`, which the check's other rules govern.

Run this file to print the digests of the current text.
"""

import hashlib
import sys
from pathlib import Path

from rust_items import is_punct, items, tokens

OUTSIDE = "<outside verus!>"

# Item -> the first 32 hex digits of the SHA-256 of its tokens, joined by
# spaces. An item's text is that of every item of that name and of what it
# nests, such as an impl's functions. OUTSIDE is every item outside
# `verus!`, with the `verus!` block's own brackets.
PINS = {
    "crates/funk-start-fds/src/record.rs": {
        OUTSIDE: "62c33443a91b98483be1c03787b79b88",
        "getfd_result": "8a11764c47df02dc60910cd9c29390f7",
        "getfd_error": "205e7fafe7fdab6640934d7d2a004358",
        "recorded": "326ffb47b78d0047a16fca535e91d8f6",
        "getfd": "d7348219c4a78f17568846590ac4dcdf",
        "Slots": "8f9306a8afb74ff8394783ad2d509b00",
        "take_slots": "0f4d1d6cf21e96e05482d5f77048a462",
        "store": "a053251f8a0ba7a82a906ae6389e9c20",
        "record_slots": "ec6ad38b80605048affda900cf3d72b4",
        "finish": "6be258f6fe1429e777f506d7ce6a4ade",
        "record": "889180278b8ce3b1478ad6bb4ad2efdf",
    },
}
# Functions pinned up to their body: their signature, clauses and
# attributes, but not the body, which Verus proves against them.
SIGNATURE_ONLY = {"record_slots"}


def pinned_text(toks, entries, name: str) -> str:
    if name == OUTSIDE:
        spans = [(e.lo, e.hi) for e in entries if not e.in_verus]
    else:
        mine = [e for e in entries if e.path == name or e.path.startswith(name + "::")]
        spans = [(e.lo, e.hi) for e in mine]
    if name in SIGNATURE_ONLY:
        spans = [(lo, body(toks, lo, hi)) for lo, hi in spans]
    return " ".join(toks[i][1] for lo, hi in spans for i in range(lo, hi))


def body(toks, lo: int, hi: int) -> int:
    return next((j for j in range(lo, hi) if is_punct(toks, j, "{")), hi)


def digests(text: str, names) -> dict[str, str]:
    toks = tokens(text)
    entries = list(items(toks, 0, len(toks)))
    return {name: digest(pinned_text(toks, entries, name)) for name in names}


def digest(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()[:32]


def pin_problems(path: str, text: str, adr: str) -> list[str]:
    pins = PINS.get(path, {})
    return [
        (
            f"{path}: {name} is not the text that {adr} pins (digest {now}, not"
            f" {pins[name]}). Verus assumes the trusted base and proves record"
            " against #117's specification, so a change to either needs a new"
            " ADR, a human ruling and the new digest, here and in that ADR"
        )
        for name, now in digests(text, pins).items()
        if now != pins[name]
    ]


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    for path, pins in PINS.items():
        text = (root / path).read_text(encoding="utf-8")
        for name, now in digests(text, pins).items():
            print(f"{path}: {name} {now}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
