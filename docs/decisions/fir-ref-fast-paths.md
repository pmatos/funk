# Current decisions: fir-ref's fast paths

This page continues [fir-ref.md](fir-ref.md). It says which spec functions
`fir-ref` runs through an implementation proved equal to them, how each works,
and what each is for. The rule that admits a fast path is ADR-2026-10-30-1450,
summed up in
[fir-ref.md](fir-ref.md#how-fir-ref-stays-equal-to-the-spec). This page is the
record: when it and an ADR disagree, the page wins, and the ADR is fixed or
deleted (ADR-2026-11-09-1610).

## Printing

`FirRef.printAttr` stands for `Attr.print`, and `FirRef.printModule` stands
for `Module.print`. The spec compiles `printDefs` before `print_eq_printAttr`
exists, so `FirRef.PrintModule` prints definitions with its own copy,
`defsText`, proved equal by `rfl`.

`FirRef.printDecimal` stands for `printInt`, through `@[csimp] theorem
printInt_eq_printDecimal` (`lean/FirRef/PrintInt.lean`). The spec's
`printInt` calls core's `Int.repr`, which divides by ten once per digit, so its
time is quadratic in the digits; a constant of `i16777215` has up to 5,050,445
of them (#41). `printDecimal` splits a number at the largest of `10^18`,
`10^36`, `10^72` and so on that is at most the number, and writes the
remainder with its leading zeros, down to parts of 18 digits. It computes each
power once, as a square. Every integer that `fir-ref` writes in a module or a
run result goes through it.

`printAttrs` inlines the spec's `printInt`, so the theorem reaches it only
because `FirRef.PrintAttr` imports `FirRef.PrintInt`. A new caller of
`printInt` in `lean/FirRef/` reaches `printDecimal` only if its module imports
`FirRef.PrintInt`, directly or through `FirRef.Fast`. The text grows in one
accumulator, appended to in place: a version that pushed each digit onto the
result of a recursive call had Lean pass the accumulator borrowed, and copy the
whole text once per part.

`scripts/check-fir-ref.sh test` checks the limit: it computes `2^16777214 - 1`
and reprints a module with it, each step under a soft limit of 30 seconds of
CPU time. Some spec functions still take time quadratic in an integer's digits:
`Tok.describe`, `readNat` and `Ty.decode`. They are compiled in `lean/Fir/`
before any `FirRef` theorem, and meet a long integer only in a text that does
not parse or decode. `fir-ref` does not run the spec's `lexAt`, because it
lexes over positions.

Rejected: a lemma on `Nat.repr` or `toString`. Core's `Int.repr` is compiled
already, so `printAttrs` would still call the slow code.

## Lexing and reading

`FirRef.parse` replaces `Fir.parse`, which the spec compiles before any theorem
of `FirRef`, so a theorem on the readers or the decoder alone would change
nothing that `fir-ref` runs. `FirRef.parse` is `readText` then
`Text.decodeModule`, and `parse_eq_parse` is proved from `readText_eq`.

`fir-ref` lexes tokens from `String` positions as the readers reach them. It
keeps neither a `List Char` nor a `List Token`, and `commentP` scans a
comment's body over positions. A `LexCursor` holds its next token, already
lexed, so each token is lexed once. Where a reader would take a token in some
branches and leave it in others, it first looks without taking (`startsOpC`,
`atLocs`) or reads on from the cursor it has. A reader written plainly there
lexes the next token twice: nothing fails, but it costs time.

The readers are written once over a `Cursor` class, and each is proved to give
what the spec's reader gives, errors included. On a `List Token` they give
`FirRef.readModule` (`readModule_eq_readModule`), and on a `LexCursor` they give
`FirRef.readText` (`readText_eq`). `lexFrom_eq` proves that the spec's `lexFrom`
is `nextTokP` then `lexFrom` again.

Accepted texts take one pass. Only when the readers fail does `FirRef.lexCheck`
run the lexer over the whole text. Its error, if any, is the parse error, and
otherwise the readers' error is, so a lexer error is still reported before any
reader error. One pass gives the spec's answer because the readers accept only
after they take `eof` (`readModule_ok_eof`), and the lexer reads `eof` only at
the end of a text it reads without an error (`nextTokP_ne_eof`). A text with a
late lexer error is slower than with the spec's lexer and readers. The human
accepted that cost on 2026-11-05: "Performance is not a deal breaker for the
lean side of things."

Rejected: an `Array` of tokens read by index. It still holds one record per
token, and needs a proof that the array holds `lex`'s list. Also rejected:
lexing only from where the readers stopped, which changes the type of every
reader and every proof about them.

`fir-ref run` reads each argument and each choice with `FirRef.argAttrP`, over
positions: `nextTokP` reads the first token, and after an integer or a word one
more step must give `eof`. It lexes at most two tokens and takes no stack per
character. `@[csimp] theorem argAttr_eq_argAttrP`, in `FirRef.Lex.Arg`, proves
it equal to `FirRef.argAttr`, the reading by the spec's lexer, for every text.
No function of the spec's lexer (`Text.lex`, `lexFrom`, `lexToken`, `utf8Len`)
is reachable from `fir-ref`'s `main`. `scripts/check-fir-ref-run.sh` checks
that an argument that is a long comment gets exit 2 on a 256 KiB stack (#135).

## Running

`FirRef.Machine.advance` runs the steps of a run in a loop of tail calls. Its
state is what the running function has left to do (`Cur`), plus one frame for
each waiting caller. Each step is one case of `Func.runOps`'s definition and
calls the same functions: the dialect's rules, `Env.operands`, `Env.bind`,
`Func.jump` and `Func.enter`. `Machine.advance_tree` proves that where the
machine stops stands for the spec's tree of the state.

`Machine.scripted`, `Machine.exhaustive` and `Machine.sampled`
(`lean/FirRef/RunModes.lean`) walk the machine's states in loops of tail calls,
exhaustive mode with a work list in the order the spec visits the paths. For
every dialect, each is proved to give what `ChoiceTree.script`, `explore` or
`sample` gives on the tree of the run. `FirRef.Run` registers them for the core
dialect, over `Core.scripted`, `Core.exhaustive` and `Core.sampled`, before
`runBytes`. `fir-ref run` reports fuel exhaustion at any budget. Its frames and
environments are on the heap, so a deep recursion costs memory, not stack.

The evidence that `fir-ref` runs the machine is in what its `main` reaches:
`lean/.lake/build/ir/FirRef/Run.c` calls the three walkers, and no copy of
`Func.runOps`, `Func.run` or the spec's modes. `Machine.c` also compiles
`Cur.denote` and `kont` for the proofs; `fir-ref` never calls them.
`lean/FirTest/RunSteps.lean` runs each mode for 1,000,000 steps on a loop and
on a recursion that never end. The modes and the machine run with memory;
[fir-ref-memory.md](fir-ref-memory.md) says how.

A new mode of `fir-ref run` needs its own walk of the machine and its own
`@[csimp]` theorem. Code that calls the spec's modes and does not import
`FirRef.Run` still runs the spec's code.

Rejected: a `@[csimp]` theorem on `Func.runOps` or `Func.run`. The modes,
compiled in the spec, would still call the spec's interpreter. Also rejected:
a machine that builds the spec's tree lazily for the spec's walks. Sampled and
exhaustive modes would still take stack for every choice.

### The bindings map

The machine keeps its values in `FirRef.Bindings`. `young` is a list of the
latest values, in front of `old`, a `Std.TreeMap` that binds each name once.
A bind puts values in front of `young`, as the spec does. A lookup searches
`young`, then `old`. A lookup that passes more than `deep` = 128 entries adds
every entry it passed to a debt. When the debt exceeds `rent` = 32 times the
length of `young`, `young` moves into `old` (`settle`), the latest value of
each name winning. `rent` and `deep` are not rules of fir or thresholds of a
check, and any values give the same results.

`Bindings.args`, `bind`, `bindResults`, `jump` and `enter` are proved to fit
`Env.operands`, `Env.bind`, `Func.jump` and `Func.enter`, with the same errors
and messages (`Bindings.Fits`, `lean/FirRef/BindingsSteps.lean`).
`Machine.runOps_congr` proves that a run depends on its environment only
through lookups. A change to those four spec operations breaks the proofs until
`Bindings` follows.

Some inputs are slower than on the spec's list, such as a run that reads one of
its oldest values just often enough to move `young`, then stops. The human
accepted that on 2026-11-05 (#47, PR #140), and on 2026-11-09 ruled that the
map stays (#169).

Rejected: one binding per name in a map on every bind. Each bind would cost a
map insert, about as much as a whole step of a run. Also rejected: a
`Std.HashMap` for `old`, since paths after a choice share their bindings and a
shared hash map copies its whole bucket array on its first insert.

## What each fast path is for

Each `@[csimp]` theorem under `lean/FirRef/` is listed with its class: depth
(the spec's function takes stack per level of nesting, per list element or per
step), speed-only, or an ordering device (`rfl`, a copy compiled after a
theorem so that `fir-ref`'s calls reach the fast path). The classes come from
reading the code and what the depth checks cover. The list is the split made
for #169, with the swaps added since.

| Theorem | Module | Class | Why |
| --- | --- | --- | --- |
| `printInt_eq_printDecimal` | `PrintInt` | speed-only | `Int.repr` is quadratic in digits |
| `problemsIn_eq_problemsIn` | `Dominance` | speed-only | The spec's `search` is a tail-call loop; [validation-fir-ref.md](validation-fir-ref.md#dominance-in-fir-ref) gives a time reason |
| `print_eq_printAttr` | `PrintAttr` | depth | The spec recurses per level |
| `print_eq_printModule` | `PrintModule` | depth | Per level and per list element |
| `decodeModule_eq_decodeModule` | `Decode` | depth | Two passes recurse per level, block and op |
| `readModule_eq_readModule` | `Read.Module` | depth | Per level and per element; only `FirTest` reaches it, since `parse_eq_parse` replaces `Fir.parse` whole |
| `parse_eq_parse` | `Parse` | depth | Carries the `LexCursor` path |
| `argAttr_eq_argAttrP` | `Lex.Arg` | depth | `utf8Len` takes stack per comment character (#135) |
| `problems_eq_locTableProblems` | `LocTable` | depth | `List.zip` recurses per entry (#136) |
| `allBlocks_eq_allBlocks` | `Validate` | depth | The spec's walk recurses per level |
| `tablesIn_eq_tablesIn` | `Tables` | depth | The spec recurses per level of nested modules |
| `allWritable_eq_writableLoop`, `dialectsAll_eq_dialectsOf` | `AttrWalk` | depth | The spec recurses per level of an applied attribute |
| `problems_eq_funcProblems`, `problems_eq_dialectItemProblems`, `problems_eq_tableProblems`, `problems_eq_moduleProblems`, `tables_eq_moduleTables` | `Validate`, `Tables` | ordering device | Copies compiled after the depth swaps |
| `wordDialects_eq_wordDialects`, `wordDialects_eq_itemWordDialects` and the four `setProblems_eq_*` | `Validate` | ordering device | The dialect-set check, compiled after the depth swaps |
| `scripted_eq_runScripted`, `exhaustive_eq_runExhaustive`, `sampled_eq_runSampled` | `Run` | depth | The machine of [Running](#running) |

The modules of `lean/FirRef/` fall in the same classes:

- **Speed-only:** `PrintInt`; `Dominance` and `Dominance/*`; the map of
  `Bindings` and `BindingsSteps` (`old`, debt, rent, `settle`, `look`,
  `runOps_congr` and the `Bindings` parts of the machine's proofs), which has
  no swap of its own.
- **Depth:** the loops of `Bindings` (`zipRev`, `zipRevH`, `zipParams`, `values`), since
  the spec's `Env.bind` and `Func.enter` use `List.zip`; `Machine`,
  `MachineTree`, `RunAt`, `Steps`, `RunModes` and `Run`; `Read/*` but
  `Read/Eof`; `Decode` and `Decode/*`; `PrintAttr`, `PrintModule`, `LocTable`,
  `Validate`, `Tables`, `AttrWalk` and `Parse`; `Lex/*` but `Lex/Cursor` and
  `Lex/Eof`, for the position-based `nextTokP`.
- **Memory, speed and depth:** `Lex/Cursor`, `Lex/Eof` and `Read/Eof`. The
  cursor took `fmt --check` of a block of 1,000,000 ops from 980 MB to 505 MB,
  and only `readText` on a `LexCursor` keeps a file parse off the spec's
  `utf8Len` on each comment body. No check covers a long comment in a file.
- **Infrastructure:** `Fast`, `Utf8` and `Except` (import order, the UTF-8
  check, proof helpers); `Main`, `RunArgs`, `Report` and `Sample`.

The speed-only parts fail the retirement test of #169: with the `@[csimp]`
removed, `fir-ref validate` of `chain.fir` and `fmt --check` of `widest.fir`
were killed at their checks' CPU limits. The spec's list in place of the map
was 264 to 758 times slower at 100,000 values, and was killed after 1,800 s at
1,000,000. The figures,
and what was not measured, are in the
[measurement comment on #169](https://github.com/pmatos/funk/issues/169#issuecomment-6749474332).
