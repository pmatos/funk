import Lake
open Lake DSL

/-
fir's Lean package: the spec's chapters as literate Lean, the `fir-ref`
executable and the Lean tests. It has no dependencies (ADR-2026-10-29-2135).
Module and declaration docs are written in Verso markup, so that the spec
document in `docs/spec/` renders them. TOML cannot set both options below,
because one name extends the other. How the package is built and tested is
docs/decisions/testing-and-harness.md#lean-tests-and-the-checks-of-fir-ref.
-/
package fir where
  leanOptions := #[
    ⟨`doc.verso, true⟩,
    ⟨`doc.verso.suggestions, false⟩
  ]

/-- The spec. -/
@[default_target]
lean_lib Fir

/-- What `fir-ref` runs beside the spec: its command line and file input. -/
lean_lib FirRef

/-- The reference interpreter's executable. -/
@[default_target]
lean_exe «fir-ref» where
  root := `FirRef.Main

/-- The cases that the use-once tests share with the Rust tests. `FirTest.UseOnce`
includes the file, and Lake does not see an included file by itself. -/
input_file useOnceCases where
  path := ".." / "tests" / "dialects" / "use-once.cases"
  text := true

/-- The cases that the effect tests share with the Rust tests, which
`FirTest.EffectCases` includes. -/
input_file effectCases where
  path := ".." / "tests" / "dialects" / "effects.cases"
  text := true

/-- The cases that the summary tests share with the Rust tests, which
`FirTest.SummaryCases` includes. -/
input_file effectSummaryCases where
  path := ".." / "tests" / "dialects" / "effect-summaries.cases"
  text := true

/-- The cases that the dialect-set tests share with the Rust tests.
`FirTest.DialectSet` includes the files. -/
input_file dialectSetCases where
  path := ".." / "tests" / "dialects" / "dialect-set.cases"
  text := true

input_file nestedModulesCases where
  path := ".." / "tests" / "dialects" / "nested-modules.cases"
  text := true

/-- The cases that the region-kind tests share with the Rust tests, which
`FirTest.RegionKindCases` includes. -/
input_file regionKindsCases where
  path := ".." / "tests" / "dialects" / "region-kinds.cases"
  text := true

/-- The cases that the tests of kinds of item share with the Rust tests,
which `FirTest.ItemKinds` includes. -/
input_file itemKindsCases where
  path := ".." / "tests" / "dialects" / "item-kinds.cases"
  text := true

/-- The cases of the text of float constants that the Lean tests share with
the Rust tests, which `FirTest.FloatText` includes. -/
input_file floatTextCases where
  path := ".." / "tests" / "dialects" / "float-text.cases"
  text := true

/-- The Lean tests: building them runs their checks. -/
@[default_target]
lean_lib FirTest where
  needs := #[`@/useOnceCases, `@/effectCases, `@/effectSummaryCases, `@/dialectSetCases,
    `@/nestedModulesCases, `@/regionKindsCases, `@/itemKindsCases, `@/floatTextCases]

/-- The paths of the package's `.lean` files, outside hidden directories such
as `.lake`, sorted, one per line. `#check_axioms` in `FirCheck` reads the same
list from the disk, and Lake would not see that read by itself. Only the
paths are traced, so adding, removing or renaming a file reruns the check, and
editing one does not rerun it by this trace. -/
target sourcePaths pkg : String := Job.async do
  let dir := pkg.dir
  let hidden (p : System.FilePath) := (p.fileName.getD "").startsWith "."
  let files ← dir.walkDir fun p => pure (p == dir || !hidden p)
  let depth := dir.components.length
  let paths := files.filter (·.extension == some "lean") |>.map fun file =>
    "/".intercalate (file.components.drop depth)
  let list := "\n".intercalate (paths.qsort (· < ·)).toList
  addPureTrace list "the paths of the Lean sources"
  return list

/-- The check that every declaration of `lean/` is trusted and every source
file is imported (ADR-2026-10-30-1452). It is a library of its own so that
only its one module reruns when the list of files changes. -/
@[default_target]
lean_lib FirCheck where
  needs := #[`@/sourcePaths]
