import Lake
open Lake DSL

/-
fir's Lean package: the spec's chapters as literate Lean. It has no
dependencies (ADR-2026-10-29-2135). Module and declaration docs are written
in Verso markup, so that the spec document in `docs/spec/` renders them.
TOML cannot set both options below, because one name extends the other.
-/
package fir where
  leanOptions := #[
    ⟨`doc.verso, true⟩,
    ⟨`doc.verso.suggestions, false⟩
  ]

@[default_target]
lean_lib Fir
