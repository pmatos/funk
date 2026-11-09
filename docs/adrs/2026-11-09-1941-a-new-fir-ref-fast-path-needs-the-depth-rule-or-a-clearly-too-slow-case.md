# A new `fir-ref` fast path needs the depth rule or a case that is clearly too slow

Status: accepted

## Context

fir's semantics exists twice in Lean: the spec in `lean/Fir/`, and what
`fir-ref` runs in `lean/FirRef/`. At commit `7369883`, `lean/FirRef/` has 55
files and 9,893 lines. `@[csimp]` theorems tie the two together
(ADR-2026-10-30-1450). [#169](https://github.com/pmatos/funk/issues/169)
says there are 41 of them. There are 15: `grep -rnE '^\s*@\[csimp\]' lean`
finds 15 lines, all under `lean/FirRef/`.

FirRef exists for two reasons. Depth is correctness: no stack per level of
nesting, per list element, per step or per call (ADR-2026-10-30-1549,
ADR-2026-11-04-2132). The other reason is speed. On 2026-11-05 the human
[ruled](https://github.com/pmatos/funk/issues/5#issuecomment-6506908304)
that speed on the Lean side is not a concern: about 10x of the Rust side on
the same job is a rough guide, hours on a simple example is not fine, and
only a case that is clearly too slow is raised.

ADR-2026-10-30-1450 came before that ruling. It asks for a fast path for
any spec function that takes stack per level "or more than linear time".

#169 asks for a split of FirRef into what depth needs and what is only for
speed, and a rule for the future. It retires a speed-only part only if the
plain spec definition stays within the 10x guide and no check turns into a
hang.

## Decision

- **A new FirRef fast path needs the depth rule, or a case that is clearly
  too slow.** More than linear time is no longer enough on its own. This
  narrows the trigger in ADR-2026-10-30-1450. "Clearly too slow" means what
  the ruling above means by it.
- **This ADR retires nothing.** The rule applies to new fast paths. Every
  part below stays as it is.
- **The split of FirRef is the two tables below.** The classes come from
  reading the code and what the depth checks cover. No depth check was run
  with a part removed. File and line references are at `7369883`; paths are
  under `lean/FirRef/`.

### The 15 swaps

| Swap | Where | Class | Why |
| --- | --- | --- | --- |
| `printInt_eq_printDecimal` | `PrintInt.lean:177` | speed-only | `Int.repr` is quadratic in digits (ADR-2026-11-03-1603); neither it nor the module claims a stack need |
| `problemsIn_eq_problemsIn` | `Dominance.lean:164` | speed-only | The spec's `search` is a tail-call loop (`lean/Fir/Validation/Search.lean:70-76`); ADR-2026-11-03-1715 gives a time reason; `check-fir-ref.sh:240` sets no small stack |
| `print_eq_printAttr` | `PrintAttr.lean:110` | depth | The spec recurses per level |
| `print_eq_printModule` | `PrintModule.lean:188` | depth | Per level and per list element; `ops` in `check-fir-ref-deep.sh` |
| `decodeModule_eq_decodeModule` | `Decode.lean:61` | depth | Two passes recurse per level, block and op |
| `readModule_eq_readModule` | `Read/Module.lean:165` | depth | The spec's readers recurse per level and per element |
| `parse_eq_parse` | `Parse.lean:76` | depth | Ordering device: the spec compiles `Fir.parse` before the theorems above |
| `argAttr_eq_argAttrP` | `Lex/Arg.lean:48` | depth | `utf8Len` takes stack per comment character ([#135](https://github.com/pmatos/funk/issues/135)); `check-fir-ref-run.sh:200` |
| `problems_eq_locTableProblems` | `LocTable.lean:45` | depth | `List.zip` recurses per entry ([#136](https://github.com/pmatos/funk/issues/136)); `check-fir-ref.sh:154` |
| `allBlocks_eq_allBlocks` | `Validate.lean:111` | depth | The spec's walk recurses per level (ADR-2026-10-30-1742) |
| `problems_eq_funcProblems` | `Validate.lean:122` | depth | `rfl` ordering device for `allBlocks` |
| `problems_eq_moduleProblems` | `Validate.lean:132` | depth | Same |
| `scripted_eq_runScripted` | `Run.lean:215` | depth | ADR-2026-11-04-2132; `check-fir-ref-run.sh:168` |
| `exhaustive_eq_runExhaustive` | `Run.lean:225` | depth | Same |
| `sampled_eq_runSampled` | `Run.lean:235` | depth | Same |

### The 55 files

| Module group | Files | Class | Note |
| --- | --- | --- | --- |
| `PrintInt` | 1 | speed-only | 181 lines |
| `Dominance`, `Dominance/*` | 8 | speed-only | 1,936 lines |
| `Bindings`, `BindingsSteps`: the map | 2 | speed-only | 680 lines in all, with the loops of the next row. The `old` map, debt, rent, `settle` and `look` (ADR-2026-11-05-0442), `runOps_congr` in `Steps`, and the `Bindings` proof parts of `Machine`, `MachineTree` and `RunModes`. It has no swap of its own |
| `Bindings`: the loops | (same) | depth | `zipRev`, `zipRevH`, `zipParams`, `values`: the spec's `Env.bind` and `Func.enter` use `List.zip` |
| `Machine`, `MachineTree`, `Steps`, `RunModes` | 4 | depth | ADR-2026-11-04-2132, apart from the `Bindings` parts above |
| `Run` | 1 | depth, infrastructure | The three run swaps; the rest is the executable's code |
| `Read/*` except `Read/Eof` | 14 | depth | Loops with explicit frames |
| `Decode`, `Decode/Scope`, `Decode/Tree` | 3 | depth | |
| `PrintAttr`, `PrintModule`, `LocTable`, `Validate`, `Parse` | 5 | depth | |
| `Lex/{Chars,Parts,Token,Next,Rest,Stream,Arg}` | 7 | depth | Needed by the position-based `nextTokP` (#135) |
| `Lex/Cursor`, `Lex/Eof`, `Read/Eof` | 3 | memory-and-speed | ADR-2026-11-03-1810: 980 MB to 505 MB. The spec's `lexFrom` is a tail-call loop. The speed ruling does not cover memory |
| `Fast`, `Utf8`, `Except` | 3 | infrastructure | Import order, the UTF-8 check, proof helpers |
| `Main`, `RunArgs`, `Report`, `Sample` | 4 | infrastructure | The executable's code, no swap |

### Measured outcome of the speed-only parts

The figures are from the
[measurement comment on #169](https://github.com/pmatos/funk/issues/169#issuecomment-6749474332):
user plus system CPU seconds, one run each on a shared host, at `7369883`.
"Plain" is the spec definition: the `@[csimp]` removed for Dominance and
PrintInt, and `deep` raised so that the map is never used for Bindings. That
last one has the cost shape of the list machine, but it is not identical
code. A kill at a limit is a lower bound.

| Part | Job | Rust side | Today's `fir-ref` | Plain | Result |
| --- | --- | --- | --- | --- | --- |
| Dominance | `validate chain.fir` | 4.91 s | 16.23 s | killed at 180 s | At least 36.6x, and the check's own limit is hit |
| Dominance | `validate exits.fir` | no figure exists | 21.45 s | killed at 240 s | The check's own limit is hit; no ratio |
| PrintInt | `fmt --check widest.fir` | 0.16 s | 3.17 s | killed at 30 s | At least 191x, as the comment reports it; `funk` keeps each spelling, so it is not identical digit work |
| PrintInt | `run max.fir`, `run widest.fir` | no counterpart | 0.75 s, 3.49 s | both killed at 30 s | Both exceed the checks' 30 s limit |
| Bindings map | 100,000 `add` ops, 100,000-step loop | no counterpart | 0.36 s, 0.13 s | 95.7 s, 97.1 s | 264x and 758x today's `fir-ref` |
| Bindings map | 1,000,000 `add` ops | no counterpart | 3.73 s | killed at 1800 s | At least 480x |
| Bindings map | 1,000,000-step loop | no counterpart | 1.16 s | killed at 1800 s | At least 1,500x |

No part passes the retirement test. Dominance and PrintInt fail it. The
Bindings map has no Rust job, so its test is "clearly too slow", and by the
reading in the comment it is that at 1,000,000 values. Whether that size
matters is the human's call. The comment's estimate of hours at that size
is extrapolated, not measured.

Not measured, as the comment says: only the named cases ran. The whole of
`check-fir-ref.sh`, `check-fir-ref-run.sh` and `check-fir-ref-deep.sh` did
not run against any throwaway build, so "no check turns into a hang" is
answered only for `check-fir-ref.sh:236-240`, `:272`, `:294` and `:296`, and
for no check of the Bindings map. No FirTest suite was built for any
throwaway. Each comparison is one run of each tool, not a median, so small
differences are noise. The memory-and-speed parts were not measured.

## Alternatives

- **Keep the trigger of ADR-2026-10-30-1450, more than linear time.** It
  asks for speed work that the ruling says is not needed.
- **Retire a part that fails the test, or loosen a check so that it
  passes.** The test exists to stop that, and the plain definitions hit the
  checks' own limits.

## Consequences

- FirRef did not get smaller from this ADR: it has 55 files and 9,893 lines
  before and after it. The acceptance line of #169 asks for a FirRef smaller
  by the retired parts, and no part passed. So whether this ADR alone closes
  #169 is still a question for the human.
- Every M1 semantic change is still written twice over the same two copies.
- A new fast path has to make its case from depth or from a clearly too
  slow case. Being faster is not enough.
- The memory-and-speed path stays outside the rule until someone asks. If a
  new one is proposed, the rule as written does not admit it for memory
  alone.
