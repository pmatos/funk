import Lean

/-!
The fingerprint of Lean declarations, which a readable block pins so that it
cannot drift from the Lean it explains (ADR-2026-11-05-2012). It covers what
a declaration says, not how it is proved:

* a theorem: its statement;
* a definition: its type and its body;
* an inductive type: its type and each constructor's name and type, and for
  a structure, the default value of each field.

It is a hash of Lean's terms, which does not depend on the names of bound
variables or on layout, so a change to a proof or to the spelling of a
binder keeps it. Any change to the declaration's own statement, body,
constructors or field defaults changes it. A definition that the
declaration only refers to counts by its name: a change to that
definition's body does not change the fingerprint. A readable block that
restates such a definition pins it as well, with `(pin := …)`.

A section's module docs pin the fingerprint of all the declarations of their
module, so that a change to what the module says fails the build until
someone reads them again.
-/

open Lean

namespace FirSpecSite

/-- The hash of what the declaration `n` says, or none when there is no such declaration. -/
def declHash (env : Environment) (n : Name) : Option UInt64 := do
  let ci ← env.find? n
  let base := hash ci.type
  match ci with
  | .defnInfo v => return mixHash base (hash v.value)
  | .opaqueInfo v => return mixHash base (hash v.value)
  | .inductInfo v =>
    let withCtors := v.ctors.foldl (init := base) fun h c =>
      match env.find? c with
      | some cc => mixHash h (mixHash (hash c) (hash cc.type))
      | none => mixHash h (hash c)
    let fields := if isStructure env n then getStructureFields env n else #[]
    let defaults := fields.foldl (init := withCtors) fun h f =>
      match env.find? (n ++ f ++ `_default) with
      | some (.defnInfo d) => mixHash h (mixHash (hash f) (hash d.value))
      | _ => h
    return defaults
  | _ => return base

/--
The fingerprint of the declarations `names`, in order, in decimal digits, or
the first name that is not a declaration. Decimal, so that no run of hex
letters reads as a misspelt word to the `typos` hook.
-/
def fingerprint (env : Environment) (names : Array Name) : Except Name String := do
  let mut h : UInt64 := 7
  for n in names do
    let some x := declHash env n | throw n
    h := mixHash h x
  return toString h

/-- The fingerprint of a module's declarations `names`, whatever their order. -/
def moduleFingerprint (env : Environment) (names : Array Name) : Except Name String :=
  fingerprint env (names.qsort Name.lt)

end FirSpecSite
