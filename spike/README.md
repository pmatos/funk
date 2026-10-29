# LeanMLIR spike prototypes (issue #24)

Throwaway code for the spike in
[#24](https://github.com/pmatos/funk/issues/24). It does not merge. The
report and the proposed ADR are on the spike's PR branch, in
`docs/spikes/leanmlir.md` and `docs/adrs/`.

| Directory | What it is | Lean |
| --- | --- | --- |
| `own/` | fir's own calculus, no dependencies | v4.35.0 |
| `leanmlir/` | the same piece as a LeanMLIR dialect, with a CFG layer | `nightly-2025-12-01` |
| `doc/` | one Verso page showing definitions from both | `nightly-2025-12-01` |

`leanmlir/` and `doc/` need a workaround before `lake update` succeeds,
because Mathlib's manifest at that nightly pins a `lean4-cli` commit that is
no longer on any branch:

```sh
lake update   # fails with git exit code 128
git -C .lake/packages/Cli fetch origin d9fc8ae23024be37424a189982c92356e37935c8
lake update && lake build
```

Render the page with `lake exe spikedoc --output _out` in `doc/`.
