# Current decisions: fir-ref, the end of a run and scripted worlds

This page continues [fir-ref-command-line.md](fir-ref-command-line.md). It
says what `fir-ref run --world` takes and prints: a scripted world, and the
trace and the end of each path as an observer sees them
([semantics-m1-trace.md](semantics-m1-trace.md),
ADR-2026-11-09-1540). It is the record: when this page and an ADR disagree,
the page wins, and the ADR is fixed or deleted (ADR-2026-11-09-1610). #213,
the harness judging memory and external calls by refinement, reads the
format below; the ADR that #213 asks for records how native runs report it.

## The option

`fir-ref run --world WORLD ...` runs the function at the scripted world that
the file WORLD holds. A WORLD of `-` is standard input, and `-` may be given
once, for the module or the world. Without `--world`, `fir-ref run` prints
what it printed before, byte for byte: M0's outputs, and every output of the
corpus, the harness and `check-fir-ref-run.sh`, are unchanged.

With `--world`, it runs the spec's modes that see the end of each return
(`Gpu.scriptedEnd`, `Gpu.exhaustiveEnd`, `Gpu.exhaustiveNaNEnd`,
`Gpu.sampledEnd`, `lean/Fir/Gpu/EndModes.lean`) by the machine
(`FirRef.Run`, [Running](fir-ref-fast-paths.md#running)). Every mode takes
it. `Gpu.observedRuns_of_memEnd` proves that a return or UB that they report
is an outcome of the spec's traced runs (`Func.observedRuns`), with an empty
trace: neither the core nor `gpu` shows an event yet.

The human ruled on 2026-11-20 (#466, Q1) that `fir-ref run` prints the end
of a run only with `--world`, and the harness passes `--world` with the
empty script on every run
([testing-and-harness.md](testing-and-harness.md#the-end-of-a-return)).
Rejected: printing the end of a run with no option, or only when it is not
empty. Either changes outputs that tests compare today, such as a kernel
that returns a pointer into work-group memory.

## Results

Each object that reports how a path ends gets, after its `values` or its
`reason`, a field `trace`, and a return also gets `escaped` and `memory`,
before `choices`:

```json
{"kind":"return","values":["ptr(1, 0)"],"trace":[],"escaped":[],
 "memory":[{"memory":0,"alloc":1,"kind":"global","align":8,"size":8,"live":true,
            "units":["frag(0, ptr(0, 0), 0)", "..."]},
           {"memory":0,"alloc":0,"kind":"global","align":1,"size":1,"live":true,
            "units":["0xff"]}],"choices":0}
```

- `trace` is the acts of the path, in order. The core and `gpu` show no
  event, so it is `[]` today. #239's external calls add the first event and
  its spelling: the callee, its arguments and the reachable bytes, and the
  world's answer.
- `escaped` lists the allocations that escaped, in the order they escaped,
  each as `{"memory":N,"alloc":A}`. Its place is the handle that the world
  names it by. Nothing escapes today.
- `memory` lists each allocation that an observer reaches (`End.Reachable`):
  every escaped allocation, each allocation that a returned pointer points
  into, and each that a unit of a live allocation reached points into. A
  pointer into a freed allocation is dangling and reaches nothing. Each entry
  gives the memory, the allocation id, the kind (`stack`, `global` or
  `heap`; `gpu.work_group_alloca` allocates a `global`), the alignment in
  units, the size in units and whether it is live. A live allocation also
  gives its `units`; a freed one does not, since only live allocations are
  compared. An id that the memory never made has `"kind":null` and nothing
  more. `FirRef.reach_iff` proves that the list is exactly the reachable
  allocations, when the walk ends within its bound of steps, which is argued,
  not proved; past it, `memory` is `null`.
- A unit is `0x` and its bits in hexadecimal, `⌈u/4⌉` digits for a unit of
  `u` bits, or `poison`, or `frag(N, ptr(A, O), I)`, the fragment `I` of a
  pointer of the memory `N`. A pointer is spelled as in `values`
  (`FirRef.ptrText`). No address is printed (`AddrRule.ignore`).

The order of `memory` is the order in which a depth-first walk first
reaches each allocation: the escaped ones, then from the returned values in
order, then from the units of each allocation in order (`FirRef.Reach`). It
takes no stack per allocation; `check-fir-ref-world.sh` runs a chain of
10,000 on a 256 KiB stack.

### How a judge compares two ends

The ids are the run's own labels, as in `values`, and are never compared.
A judge compares two ends as `End.SeenUnder` does: it builds a one-to-one
renaming from the source's side, starting from the escaped lists, which
must have the same length and are matched place by place, and from the
returned values. A returned or stored pointer of the source with
provenance whose allocation is not in its `memory` is dangling, and any
value of the target refines it. A pointer of the source is matched with the
target's pointer at the same place; each pair of matched allocations must
agree on kind, alignment, size and liveness, and, while live, each unit of
the source must be refined by the target's, a `poison` by anything. The
target may reach more allocations than the source, where the source has
poison; the judge ignores them.

Rejected: renumbering allocations by the order of the walk, so that equal
ends print the same text. A target that holds a pointer where the source
has poison reaches more allocations, and its numbering would then differ
from the source's after it.

## The scripted world

WORLD is UTF-8 text, one line at a time:

- `answer V...` starts the answer to the next event: its results, each
  spelled as `fir-ref run` spells a value;
- `store H O U...` writes the units `U...`, spelled as above but with
  `frag(M,H,O,I)` naming the escaped allocation by its handle `H`, or `none`,
  into the escaped allocation of handle `H`, from the offset `O`;
- `alloc M N K` creates a heap allocation of `N` units aligned to `2^K` in
  the memory `M`, which escapes at once;
- `free H` frees the escaped heap allocation of handle `H`.

Each action belongs to the answer before it (`WorldAct`,
`lean/Fir/Execution/TraceWorld.lean`). A blank line, or one whose first
word starts with `#`, says nothing. An action before any answer, or a line
that is none of these, is an error: `fir-ref: WORLD: line N: ...` on
standard error and exit status 2.

A script fits a path when it answers exactly the events that the path
shows, in order (`TOutcome.Follows`, `TOutcome.follows_iff`,
`lean/Fir/Execution/TraceScript.lean`). A script that does not fit is an
argument error, as a choice sequence that does not fit is: `fir-ref: @f:
the world's script does not fit the run: ...` on standard error, nothing on
standard output, and exit status 2. The core and `gpu` show no event, so
the empty script fits every run and a script that answers an event fits
none.

What #239 adds: the core's first event, an external call, so that a
script's answers are read at their result types, the world's actions are
applied, and `trace` and `escaped` fill. The spec's tests of answers in
order and of writes into escaped memory are in `lean/FirTest/WorldScript.lean`.

Rejected: a JSON script. Lean's JSON reader takes stack per level of
nesting, and `fir-ref` must take none per element of its input.
