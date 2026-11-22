# What the corpus texts test: globals

This page continues [texts.md](texts.md): it lists the texts of the fir
test corpus that test globals and their address `globaladdr` (#237), in
the order their stages added them. Paths are relative to `tests/fir/`.

The texts of #237's first stage hold globals, core items of units and
addresses
([ADR-2026-11-19-0124](../adrs/2026-11-19-0124-a-global-is-a-core-item-of-units-and-addresses.md)).
`globals` holds constant, exported and all-zero globals of the default
memory, a table of pointers and a global that points into itself, beside a
function that runs on both sides. `globals-memories` holds globals of a
memory of 16-bit units and of a nested module. `reject/global.toml` holds
the texts that do not decode and those that validation rejects. Stage 2a
made a run start with its table's globals, so a run's own allocations take
the ids after them.

The texts of #237's second stage use `globaladdr`. `globaladdr` reads a
constant global unit by unit, the zeros past its initializer included,
follows a table of pointers held by `addr` pieces, writes a global through
a pointer that the table holds, and stores to a constant global, which is
UB. `globaladdr-memories` does the same in a memory of 16-bit units and in
a nested module, whose run holds its own table's globals only.
`reject/globaladdr.toml` holds the texts that do not decode and those that
name no global of the op's table or a global of another memory.

#237's third stage places globals in native code
([x86-64-backend-lowering-memory.md](../decisions/x86-64-backend-lowering-memory.md#globals)),
so each test of `globaladdr` whose run is not UB runs as native code too,
`@addresses`, which returns three globals' addresses, among them (#213
stage 2). `globals-programs` runs programs on both: a
constant, exported table of pointers at offsets into an array, a list of
nodes linked by `addr` pieces and walked in a loop, a counter that a called
function bumps on each pass of a loop, a copy of a constant global into an
all-zero exported one, a global that points into itself, whose two
addresses differ by 8, and a global of a second memory of bytes, aligned to
256, whose address modulo 256 is 0 under every address policy. No test
returns an address. The tests of `globals-memories` and
`globaladdr-memories` stay interpreter-only, since the backend realises
neither a memory of 16-bit units nor a nested module's functions.
