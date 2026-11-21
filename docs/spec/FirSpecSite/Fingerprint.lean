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
constructors or field defaults changes it.

A definition's body includes the helpers that Lean generates to hold part
of it, since its stored value only names them. These are the body of a
recursive definition (`f._f`, `f._unary`, or `f._mutual`, which holds the
whole mutual block), its case splits (`f._sparseCasesOn_1`), and its
pattern matchers (`f.match_1`), followed transitively, so a recursive
definition of a mutual block covers the bodies of the whole block. A
helper counts by its type and value, not by its name: Lean may reuse a
matcher made for another definition of the same shape, or name the helper
afresh when that definition goes, and neither changes the fingerprint. Any
other definition that the declaration only refers to counts by its name: a
change to that definition's body does not change the fingerprint. A
readable block that restates such a definition pins it as well, with
`(pin := …)`.

A section's module docs pin the fingerprint of all the declarations of their
module, so that a change to what the module says fails the build until
someone reads them again.
-/

open Lean

namespace FirSpecSite

/--
Whether `c` is a definition that Lean generated to hold part of another: a
pattern matcher, or a definition whose name ends in a component that starts
with `_`. A theorem is never one, so that proofs stay out of the fingerprint.
-/
def isHelper (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some (.defnInfo _) =>
    Meta.isMatcherCore env c || match c with
      | .str _ s => s.startsWith "_"
      | _ => false
  | _ => false

/-- `e` with each helper in `hashes` replaced by a placeholder that carries its hash and keeps its universe levels. -/
def withHelperHashes (hashes : NameMap UInt64) (e : Expr) : Expr :=
  e.replace fun
    | .const c us => (hashes.find? c).map fun h => .const (.num `_helper h.toNat) us
    | _ => none

mutual
/--
The hash of the helper `c`: its type and its value, but not its name. The
state keeps the hash of each helper met. Helpers form no cycle, since Lean
adds a definition only after every constant it uses, so this ends.
-/
partial def helperHash (env : Environment) (c : Name) : StateM (NameMap UInt64) UInt64 := do
  if let some h := (← get).find? c then return h
  let some ci := env.find? c | return 0
  let value ← match ci.value? with
    | some v => contentHash env v
    | none => pure 0
  let h := mixHash (← contentHash env ci.type) value
  modify (·.insert c h)
  return h

/-- The hash of `e`, in which each helper counts by its hash, not by its name. -/
partial def contentHash (env : Environment) (e : Expr) : StateM (NameMap UInt64) UInt64 := do
  let mut hashes : NameMap UInt64 := {}
  for c in e.getUsedConstants do
    if isHelper env c then
      hashes := hashes.insert c (← helperHash env c)
  return hash (withHelperHashes hashes e)
end

/-- The hash of the definition body `e`, with the type and value of each helper it reaches. -/
def bodyHash (env : Environment) (e : Expr) : UInt64 :=
  (contentHash env e).run' {}

/-- The hash of what the declaration `n` says, or none when there is no such declaration. -/
def declHash (env : Environment) (n : Name) : Option UInt64 := do
  let ci ← env.find? n
  let base := hash ci.type
  match ci with
  | .defnInfo v => return mixHash base (bodyHash env v.value)
  | .opaqueInfo v => return mixHash base (bodyHash env v.value)
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
