"""How the harness relates the end of a native run to fir-ref's
(docs/decisions/testing-and-harness.md#native-runs-report-memory).

Run with `--memory`, a built executable reports, after its values, every
global of the module: its name, memory, address and units
(docs/decisions/x86-64-backend-executable.md#reporting-memory). Native code
calls nothing outside the module yet, so nothing escapes and its trace is
empty, and its stack allocations are freed when the function returns: the
memory an observer can reach in it is its globals.

The harness compares the two ends as `ends` does, by a one-to-one renaming
built from fir-ref's side, with the target's allocations the globals. A
pointer of fir-ref's into an allocation it lists, at offset O, is related
to the native global whose address plus O is the native pointer's address,
as the human ruled on 2026-11-22 (#213, Q2). Only the run's own addresses
are related to each other; none is compared with fir-ref's, since the spec
gives addresses that native code need not (#232). A global is compared with
its source allocation unit by unit: a unit of bits as its byte, and the
fragment I of a pointer as byte I of the native address, read from the
pointer's whole bytes where fir-ref holds all its fragments in order.
What the harness cannot relate, such as a pointer with no provenance,
whose offset is fir-ref's address, makes the test invalid.
"""

import bisect
import re
from dataclasses import dataclass

import ends

# The x86-64 backend realises memories of 8-bit units and 64-bit
# little-endian pointers only, so a pointer takes 8 units, fragment I being
# byte I of its address.
POINTER_UNITS = 8
UNITS = re.compile(r"(?:[0-9a-f]{2}|zeros\((?:0|[1-9][0-9]*)\))*")
DECIMAL = ends.DECIMAL
PIECE = re.compile(r"([0-9a-f]{2})|zeros\(([0-9]+)\)")


class Units:
    """A global's units as its report gives them, runs of bytes and of
    zeros, read one at a time without spelling out the zeros: a global may
    take 2^30 of them, and most runs compare none."""

    def __init__(self, pieces):
        self.starts = []
        self.pieces = []
        size = 0
        for p in pieces:
            n = p if isinstance(p, int) else len(p)
            if n:
                self.starts.append(size)
                self.pieces.append(p)
                size += n
        self.size = size

    def __len__(self) -> int:
        return self.size

    def __getitem__(self, i: int) -> int:
        if not 0 <= i < self.size:
            raise IndexError(i)
        k = bisect.bisect_right(self.starts, i) - 1
        p = self.pieces[k]
        return 0 if isinstance(p, int) else p[i - self.starts[k]]

    def __bytes__(self) -> bytes:
        return b"".join(bytes(p) for p in self.pieces)

    def __eq__(self, other) -> bool:
        return isinstance(other, (Units, bytes)) and bytes(self) == bytes(other)

    __hash__ = None


@dataclass(frozen=True)
class Global:
    """A global of the module as a native run reports it: its units are
    `bytes` or `Units`."""

    name: str
    memory: int
    address: int
    units: bytes | Units


def read_units(text: str) -> Units | None:
    """The units of a global's `units` text: two hexadecimal digits a byte,
    and `zeros(N)` for N zero bytes; or None when it is not such a text."""
    if UNITS.fullmatch(text) is None:
        return None
    pieces = []
    for m in PIECE.finditer(text):
        if m.group(1) is None:
            pieces.append(int(m.group(2)))
        elif pieces and isinstance(pieces[-1], bytearray):
            pieces[-1].append(int(m.group(1), 16))
        else:
            pieces.append(bytearray([int(m.group(1), 16)]))
    return Units(pieces)


class Unrelated(Exception):
    """A part of fir-ref's end that the harness cannot relate to the
    native run, so the test proves nothing."""


class _Native(ends._Renaming):
    def __init__(self, source: ends.End, globals_: tuple[Global, ...]):
        self.globals = {(g.memory, i): g for i, g in enumerate(globals_)}
        memory = tuple(
            ends.Alloc(g.memory, i, "global", 0, len(g.units), True)
            for (_, i), g in self.globals.items()
        )
        super().__init__(source, ends.End(memory=memory))
        # Fragments whose pointer's allocation was not yet renamed.
        self.later = []

    def image(self, s, offset, got):
        """The global whose address plus `offset` is the address `got`;
        when several are, one already renamed from `s`, else one of `s`'s
        size that nothing is renamed into."""
        if DECIMAL.fullmatch(got) is None:
            return None
        address = int(got) % 2**64
        found = [
            t
            for t, g in self.globals.items()
            if t[0] == s[0] and (g.address + offset) % 2**64 == address
        ]
        if not found:
            return None
        size = self.source[s].size
        for pick in (
            lambda t: self.forward.get(s) == t,
            lambda t: t not in self.backward and len(self.globals[t].units) == size,
            lambda t: t not in self.backward,
        ):
            for t in found:
                if pick(t):
                    return t
        return found[0]

    def pointer(self, memory, want, got, where):
        if want.startswith("ptr(none,"):
            raise Unrelated(
                f"{where} is {want}, a pointer with no provenance, whose offset"
                " is fir-ref's address"
            )
        return super().pointer(memory, want, got, where)

    def fields(self, a, b, t, name):
        if a.kind is None:
            raise Unrelated(f"{name} is an id that fir-ref's memory never made")
        why = super().fields(a, b, t, name, ("kind", "size", "live"))
        if why is not None:
            return why
        g = self.globals[t]
        if a.align and g.address % a.align:
            return (
                f"{name} has align {a.align}, and the target's global {g.name}"
                f" is at {g.address}"
            )
        return None

    def units(self, a, t, name):
        g = self.globals[t]
        for p, want in enumerate(a.units):
            where = f"unit {p} of {name}"
            got = g.units[p]
            frag = ends.FRAGMENT.fullmatch(want)
            if frag is None:
                if want not in (ends.POISON, f"0x{got:02x}"):
                    return (
                        f"{where} is 0x{got:02x} in the target's {g.name}, not {want}"
                    )
                continue
            why = self.fragment(a, g, p, frag.groups(), where)
            if why is not None:
                return why
        return None

    def fragment(self, a, g, p, parts, where) -> str | None:
        """Compares the byte `p` of the native global `g` with the fragment
        `parts`, `(memory, alloc, offset, index)`, at `p` of `a`."""
        memory, alloc, offset, index = parts
        if alloc == "none":
            raise Unrelated(
                f"{where} is a part of ptr(none, {offset}), a pointer with no"
                " provenance, whose bytes are fir-ref's address"
            )
        s = self.reached(int(memory), alloc)
        if s is None:
            return None
        start = p - int(index)
        whole = a.units[max(start, 0) : start + POINTER_UNITS]
        mine = [
            f"frag({memory}, ptr({alloc}, {offset}), {i})" for i in range(POINTER_UNITS)
        ]
        if start >= 0 and list(whole) == mine:
            if int(index) != 0:
                return None
            whole = bytes(g.units[j] for j in range(p, p + POINTER_UNITS))
            address = int.from_bytes(whole, "little")
            return self.pointer(
                int(memory), f"ptr({alloc}, {offset})", str(address), where
            )
        if s not in self.forward:
            self.later.append((s, int(offset), int(index), g.units[p], where))
            return None
        return self.byte(s, int(offset), int(index), g.units[p], where)

    def byte(self, s, offset, index, got, where) -> str | None:
        """Checks that the native byte `got` is byte `index` of the address
        of `s`'s image plus `offset`."""
        g = self.globals[self.forward[s]]
        want = ((g.address + offset) % 2**64 >> (8 * index)) & 0xFF
        if got != want:
            return (
                f"{where} is 0x{got:02x}, not byte {index} of the address of"
                f" the target's {g.name} plus {offset}"
            )
        return None

    def rest(self) -> str | None:
        """Checks the fragments left for later, once the renaming is built."""
        for s, offset, index, got, where in self.later:
            if s not in self.forward:
                raise Unrelated(
                    f"{where} is a part of a pointer whose allocation the harness"
                    " cannot relate to a native global"
                )
            why = self.byte(s, offset, index, got, where)
            if why is not None:
                return why
        return None


def refined(
    source: ends.End, want, globals_: tuple[Global, ...], got, types
) -> tuple[str, bool] | None:
    """Why the native run's end, its returned values `got` and the globals
    `globals_` it reports, does not refine fir-ref's end `source`, with the
    values `want`: the reason, and whether it makes the test invalid rather
    than failed. None when it refines. `types` are the result types; only
    pointer values and memory are compared here."""
    r = _Native(source, globals_)
    try:
        why = r.refined(want, got, types) or r.rest()
    except Unrelated as e:
        return f"{e}, so the test proves nothing", True
    return None if why is None else (why, False)
