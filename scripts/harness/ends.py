"""How the harness compares the ends of two returns (ADR-2026-11-09-1540).

`fir-ref run --world` reports, at a return, the trace of the path, the
allocations that escaped and the memory that an observer reaches
(docs/decisions/fir-ref-run-end.md#results). The end of a target's return
refines the source's when a one-to-one renaming of allocations, built from
the source's side, shows the source's end in it, as `End.SeenUnder` does
(docs/decisions/fir-ref-run-end.md#how-a-judge-compares-two-ends):

- the escaped lists have the same length and are matched place by place;
- each pointer of the source, returned or stored, into an allocation that
  its `memory` lists is matched with the target's at the same place, at the
  same offset; any other, a dangling one, is poison;
- each matched pair agrees on kind, alignment, size and liveness, and while
  live each unit of the source is refined by the target's, `poison` by
  anything.

Ids are the runs' own labels and are never compared, and neither is an
address. The target may reach more allocations than the source; only those
the renaming reaches are compared. A path that shows events is not judged
here yet: #239 gives an external call its spelling. `native_ends` relates
a native run's addresses and globals to the source's end through the
same renaming.
"""

import re
from collections import deque
from dataclasses import dataclass

POISON = "poison"
# A signed decimal, as an integer value or an address is spelled.
DECIMAL = re.compile(r"-?(0|[1-9][0-9]*)")
POINTER = re.compile(r"ptr\((none|[0-9]+), (-?[0-9]+)\)")
FRAGMENT = re.compile(r"frag\(([0-9]+), ptr\((none|[0-9]+), (-?[0-9]+)\), ([0-9]+)\)")
POINTER_TYPE = re.compile(r"ptr(?:\(([0-9]+)\))?")


@dataclass(frozen=True)
class Alloc:
    """An allocation that an observer reaches: `kind` is None for an id
    that the memory never made, and `units` are given while it is live."""

    memory: int
    alloc: int
    kind: str | None
    align: int = 0
    size: int = 0
    live: bool = False
    units: tuple[str, ...] = ()


@dataclass(frozen=True)
class End:
    """The trace of a path and, at a return, the allocations that escaped,
    each as `(memory, alloc)`, and the memory an observer reaches, or None
    when fir-ref's walk of it ran out of steps."""

    trace: tuple = ()
    escaped: tuple[tuple[int, int], ...] = ()
    memory: tuple[Alloc, ...] | None = ()


# The end of a return that shows no event, lets nothing escape and reaches
# no allocation.
NOTHING = End()


def pointer_memory(ty: str) -> int | None:
    """The memory of the pointer type `ty`: 0 for `ptr`, N for `ptr(N)`;
    None for any other type."""
    m = POINTER_TYPE.fullmatch(ty)
    if m is None:
        return None
    return int(m.group(1) or 0)


class Renaming:
    """A renaming of the source's allocations into the target's, built from
    the source's side. A subclass that reads the target another way
    overrides `image`, `fields` and `units`."""

    def __init__(self, source: End, target: End):
        self.source = {(a.memory, a.alloc): a for a in source.memory}
        self.target = {(a.memory, a.alloc): a for a in target.memory or ()}
        self.source_escaped = source.escaped
        self.target_escaped = target.escaped
        self.forward = {}
        self.backward = {}
        self.todo = deque()

    def reached(self, memory: int, alloc: str) -> tuple[int, int] | None:
        """The source's allocation that a pointer with provenance points
        into, or None for a dangling pointer, which is poison in the
        comparison: one into an allocation that the observer does not
        reach, or into a freed one (`FirRef.reachOf`)."""
        a = self.source.get((memory, int(alloc)))
        if a is None or (a.kind is not None and not a.live):
            return None
        return memory, int(alloc)

    def match(self, s: tuple[int, int], t: tuple[int, int]) -> str | None:
        if s[0] != t[0]:
            return f"allocation {s[1]} of memory {s[0]} is renamed into memory {t[0]}"
        if self.forward.get(s, t) != t or self.backward.get(t, s) != s:
            return f"no one-to-one renaming relates allocation {s[1]} of memory {s[0]}"
        if s not in self.forward:
            self.forward[s] = t
            self.backward[t] = s
            self.todo.append(s)
        return None

    def pointer(self, memory: int, want: str, got: str, where: str) -> str | None:
        """Matches the source's pointer `want` with the target's `got`."""
        if want == POISON:
            return None
        w = POINTER.fullmatch(want)
        if w is None:
            return f"{where}, {want}, is not a pointer"
        if w.group(1) == "none":
            return None if got == want else f"{where} is {got}, not {want}"
        s = self.reached(memory, w.group(1))
        if s is None:
            return None
        t = self.image(s, int(w.group(2)), got)
        if t is None:
            return (
                f"{where} points into allocation {s[1]} of memory {s[0]}, which"
                f" an observer reaches, and the target's is {got}"
            )
        return self.match(s, t)

    def image(
        self, s: tuple[int, int], offset: int, got: str
    ) -> tuple[int, int] | None:
        """The target's allocation that its pointer `got` points into, at
        the source's `offset`, where the source's points into `s`; or None
        when it points elsewhere."""
        g = POINTER.fullmatch(got)
        if g is None or g.group(1) == "none" or int(g.group(2)) != offset:
            return None
        return s[0], int(g.group(1))

    def unit(self, want: str, got: str, where: str) -> str | None:
        w = FRAGMENT.fullmatch(want)
        if w is None:
            return None if want in (POISON, got) else f"{where} is {got}, not {want}"
        memory, alloc, offset, index = w.groups()
        if alloc == "none":
            return None if got == want else f"{where} is {got}, not {want}"
        if self.reached(int(memory), alloc) is None:
            return None
        g = FRAGMENT.fullmatch(got)
        if g is None or (g.group(1), g.group(3), g.group(4)) != (memory, offset, index):
            return f"{where} is {got}, not a fragment like {want}"
        target = f"ptr({g.group(2)}, {offset})"
        return self.pointer(int(memory), f"ptr({alloc}, {offset})", target, where)

    def seen(self, s: tuple[int, int]) -> str | None:
        """Compares the source's allocation `s` with its image."""
        t = self.forward[s]
        a, b = self.source.get(s), self.target.get(t)
        name = f"allocation {s[1]} of memory {s[0]}"
        if a is None:
            return f"fir-ref lets {name} escape, and its memory does not list it"
        if b is None:
            return f"the target reaches nothing where fir-ref reaches {name}"
        why = self.fields(a, b, t, name)
        if why is not None or not a.live:
            return why
        return self.units(a, t, name)

    def fields(
        self,
        a: Alloc,
        b: Alloc,
        t: tuple[int, int],
        name: str,
        which=("kind", "align", "size", "live"),
    ) -> str | None:
        """Compares the fields `which`, by default the kind, alignment, size
        and liveness, of the source's allocation `a`, called `name`, with
        its image `b`, of key `t`."""
        for field in which:
            if getattr(a, field) != getattr(b, field):
                return (
                    f"{name} has {field} {getattr(a, field)}, and the target's"
                    f" {getattr(b, field)}"
                )
        return None

    def units(self, a: Alloc, t: tuple[int, int], name: str) -> str | None:
        """Compares the units of the source's live allocation `a`, called
        `name`, with those of its image, of key `t`."""
        for i, (want, got) in enumerate(zip(a.units, self.target[t].units)):
            why = self.unit(want, got, f"unit {i} of {name}")
            if why is not None:
                return why
        return None

    def refined(self, want, got, types) -> str | None:
        """Why the target's end, with the returned values `got`, does not
        refine the source's, with `want`: `refined` below."""
        if len(self.source_escaped) != len(self.target_escaped):
            return (
                f"fir-ref's run lets {_count(self.source_escaped, 'allocation')}"
                f" escape and the target's {len(self.target_escaped)}"
            )
        for s, t in zip(self.source_escaped, self.target_escaped):
            why = self.match(s, t)
            if why is not None:
                return why
        for i, (w, g, ty) in enumerate(zip(want, got, types), 1):
            memory = pointer_memory(ty)
            if memory is not None:
                why = self.pointer(memory, w, g, f"value {i}")
                if why is not None:
                    return why
        while self.todo:
            why = self.seen(self.todo.popleft())
            if why is not None:
                return why
        return None


def _count(items, noun: str) -> str:
    return f"{len(items)} {noun}{'' if len(items) == 1 else 's'}"


def unjudged(source: End, target: End) -> str | None:
    """Why the harness cannot judge the two ends, so the test proves
    nothing: fir-ref's walk of the memory ran out of steps, or a path shows
    events, which the harness does not judge yet (#213, stage 3)."""
    if source.memory is None:
        return "fir-ref's walk of the memory an observer reaches ran out of steps"
    if source.trace or target.trace:
        return (
            f"fir-ref's path shows {_count(source.trace, 'event')} and the"
            f" target's {len(target.trace)}, and the harness judges no event yet"
        )
    return None


def refined(source: End, want, target: End, got, types) -> str | None:
    """Why the target's end, with the returned values `got`, does not refine
    the source's, with `want`, or None when it does, where both ends are
    spelled as `fir-ref run --world` spells them. `types` are the result
    types, and only pointer values are compared. The harness judges a
    native end with `native_ends.refined`, through the same renaming; this
    one states the rule on two of fir-ref's ends. The harness can judge
    both ends (`unjudged`)."""
    return Renaming(source, target).refined(want, got, types)
