# An op reads the layout entry of the memory it accesses

Status: accepted
Tier: direction; area: semantics

## Decision

- **A run gives each memory its layout entry.** A dialect's semantics with
  memory (`DialectMemDenote.denoteAt`) takes `lay : N → MemLayout`, the
  entry of each memory of the run, beside the map `ρ` from the dialect's
  memory names to the run's. A memory's units are as wide as its entry says
  (`unitsOf lay`). The entry is the data layout's whole `MemLayout`
  (ADR-2026-11-12-1821); its `mem` field is not read.
- **An op reads its memory's entry.** An op that names the dialect's memory
  `x` accesses the run's memory `ρ x` and takes its unit width, byte order
  and pointer width from `lay (ρ x)`: never from the dialect, nor from a
  parameter of the op.
- **A module runs with its own layout.** `DataLayout.entry` gives memory
  `n` its declared entry, or `MemLayout.default`'s when there is none. The
  core's modes run a module at `M.layout.entry`, naming the core's memories
  by their numbers, so `fir-ref` runs each module with the widths and byte
  orders it declares.
- **The obligations hold at every layout.** The effect, totality,
  monotonicity and poison obligations, `LiftsSetM` and the theorems on runs
  with memory quantify over `lay` as they do over `ρ`.

## Why

The same units decode to different values in 8-bit little-endian and in
16-bit big-endian memory. The review of the encodings (#357) found that
free unit and byte-order parameters let a caller decode with the wrong
ones; reading them from the accessed memory's entry rules that out.

## Rejected alternatives

- **A unit width per memory, and the byte order as a second map.** The two
  maps could disagree with each other and with the module's layout.
- **Fix `Func.memRuns` to the module's numbers and layout.** A dialect's
  memories reach a run through `ρ` under any names, as in a sum, so the
  theorems stay general; the core's modes choose the module's.
