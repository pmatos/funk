import Lake
open Lake DSL

/-
fir's Lean package: the spec's chapters as literate Lean, the `fir-ref`
executable and the Lean tests. It has no dependencies (ADR-2026-10-29-2135).
Module and declaration docs are written in Verso markup, so that the spec
document in `docs/spec/` renders them. TOML cannot set both options below,
because one name extends the other. How the package is built and tested is
ADR-2026-10-30-1250.
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

/-- The Lean tests: building them runs their checks. -/
@[default_target]
lean_lib FirTest
