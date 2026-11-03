import Fir.Text.ReadAcceptedModule
import Fir.Text.DecodeScope

/-!
# The first pass names each value once

The last step of the parser decodes a tree in two passes. The first builds
a function's scope: it adds each definition of the function, at any depth,
and rejects a value that is already in the scope, at its second definition.
So when the pass succeeds, the function names each value once.

`Adds define decode defs a` says what the first pass does with a part `a` of
the tree, a list of blocks, ops or regions. When the pass adds `a` to a
scope that holds the definitions `L`, with no name twice, and the second
pass decodes `a` as `x`, the scope it gives holds `L ++ defs x`, with no
name twice. `defs` is `Block.scopeDefs`, `Operation.scopeDefs` or
`Region.scopeDefs`: the definitions of the decoded blocks, ops or regions,
in the order that the first pass reads them. Both passes decode each
definition with `decodeDef`, so the first pass adds exactly the definitions
that the second gives the function. `Func.scopeDefs_perm` then makes them,
with the parameters, a permutation of `Func.defs`, as in the round trip.

As in the round trip's proof (ADR-2026-11-03-0028), the lemmas for blocks,
ops and regions take what the pass does with the parts they hold as
hypotheses, and three short mutual theorems tie them together by
structural recursion on the tree.
-/

namespace Fir.Text

variable {d : Dialect}

/-- A value that a scope does not contain is not named in the list that the
scope holds. -/
theorem Scope.Holds.not_mem {sc : Scope d} {L : List (Name × d.Ty)} (h : sc.Holds L) {n : Name}
    (hn : sc.contains n = false) : n ∉ L.map (·.1) := by
  intro hm
  obtain ⟨⟨_, t⟩, hy, rfl⟩ := List.mem_map.mp hm
  rw [Std.HashMap.contains_eq_isSome_getElem?, (h _ t).mpr hy] at hn
  cases hn

variable [DialectText d]

/-- When `define` succeeds on a scope that holds `L`, with no name twice, the
scope it gives holds `L` and the definitions that it decodes, with no name
twice. -/
theorem define_holds : ∀ {xs : List SDef} {sc sc' : Scope d} {L ys : List (Name × d.Ty)},
    define sc xs = .ok sc' → xs.mapM decodeDef = .ok ys → sc.Holds L → (L.map (·.1)).Nodup →
      sc'.Holds (L ++ ys) ∧ ((L ++ ys).map (·.1)).Nodup
  | [], sc, sc', L, ys, h, hm, hsc, hnd => by
    rw [define] at h
    cases h
    cases hm
    simpa using ⟨hsc, hnd⟩
  | x :: xs, sc, sc', L, ys, h, hm, hsc, hnd => by
    rw [define] at h
    bind_step h with ⟨⟨n, t⟩, h₁, h⟩
    dsimp only at h
    split at h
    · cases h
    rename_i hc
    rw [List.mapM_cons, h₁, ok_bind] at hm
    bind_step hm with ⟨ys', h₂, hm⟩
    cases hm
    have hn := hsc.not_mem (Bool.eq_false_iff.mpr hc)
    have hnd' : ((L ++ [(n, t)]).map (·.1)).Nodup := by
      rw [List.map_append, List.nodup_append]
      exact ⟨hnd, by simp, fun a ha b hb => by simp at hb; subst hb; exact fun he => hn (he ▸ ha)⟩
    obtain ⟨k, k'⟩ := define_holds h h₂ (hsc.insert hn) hnd'
    simp only [List.append_assoc, List.singleton_append] at k k'
    exact ⟨k, k'⟩

/-- The first pass over `a` adds to any scope that holds `L` the
definitions that the second pass decodes, in the order `defs` lists them,
and finds no value twice. -/
def Adds {α β : Type} (define : Scope d → α → Except ParseError (Scope d))
    (decode : Scope d → String → α → Except ParseError β) (defs : β → List (Name × d.Ty))
    (a : α) : Prop :=
  ∀ {sc sc' sc₂ g L x}, define sc a = .ok sc' → decode sc₂ g a = .ok x → sc.Holds L →
    (L.map (·.1)).Nodup → sc'.Holds (L ++ defs x) ∧ ((L ++ defs x).map (·.1)).Nodup

/-- The first pass adds nothing for no blocks. -/
theorem adds_blocks_nil : Adds (d := d) defineBlocks decodeBlocks Block.scopeDefs [] := by
  intro sc sc' sc₂ g L x h₁ h₂ hsc hnd
  rw [defineBlocks] at h₁
  rw [decodeBlocks] at h₂
  cases h₁
  cases h₂
  simpa [Block.scopeDefs] using ⟨hsc, hnd⟩

/-- The first pass adds a block's arguments, then its ops' definitions, then
those of the blocks after it, when it adds those of the ops and of the
blocks after it. -/
theorem adds_blocks_cons {label : Name} {params : List SDef} {ops : List SOp} {sbs : List SBlock}
    (hops : Adds (d := d) defineOps decodeOps Operation.scopeDefs ops)
    (hbs : Adds (d := d) defineBlocks decodeBlocks Block.scopeDefs sbs) :
    Adds (d := d) defineBlocks decodeBlocks Block.scopeDefs (⟨label, params, ops⟩ :: sbs) := by
  intro sc sc' sc₂ g L x h₁ h₂ hsc hnd
  rw [defineBlocks] at h₁
  bind_step h₁ with ⟨sc₁, e₁, h₁⟩
  bind_step h₁ with ⟨sc₃, e₂, e₃⟩
  rw [decodeBlocks] at h₂
  bind_step h₂ with ⟨ps, f₁, h₂⟩
  bind_step h₂ with ⟨os, f₂, h₂⟩
  bind_step h₂ with ⟨bs, f₃, h₂⟩
  cases h₂
  obtain ⟨k₁, n₁⟩ := define_holds e₁ f₁ hsc hnd
  obtain ⟨k₂, n₂⟩ := hops e₂ f₂ k₁ n₁
  obtain ⟨k₃, n₃⟩ := hbs e₃ f₃ k₂ n₂
  simp only [Block.scopeDefs, List.append_assoc] at k₃ n₃ ⊢
  exact ⟨k₃, n₃⟩

/-- The first pass adds nothing for no ops. -/
theorem adds_ops_nil : Adds (d := d) defineOps decodeOps Operation.scopeDefs [] := by
  intro sc sc' sc₂ g L x h₁ h₂ hsc hnd
  rw [defineOps] at h₁
  rw [decodeOps] at h₂
  cases h₁
  cases h₂
  simpa [Operation.scopeDefs] using ⟨hsc, hnd⟩

/-- The first pass adds an op's results, then the definitions of its regions,
then those of the ops after it, when it adds those of the regions and of
the ops after it. Its operands are not looked up in this pass. -/
theorem adds_ops_cons {results : List SDef} {name : String} {namePos : TextPos} {attrs : List Attr}
    {operands : List (Name × TextPos)} {succs : List Succ} {regions : List SRegion} {loc : LocRef}
    {sos : List SOp}
    (hreg : Adds (d := d) defineRegions decodeRegions Region.scopeDefs regions)
    (hos : Adds (d := d) defineOps decodeOps Operation.scopeDefs sos) :
    Adds (d := d) defineOps decodeOps Operation.scopeDefs
      (⟨results, name, namePos, attrs, operands, succs, regions, loc⟩ :: sos) := by
  intro sc sc' sc₂ g L x h₁ h₂ hsc hnd
  rw [defineOps] at h₁
  bind_step h₁ with ⟨sc₁, e₁, h₁⟩
  bind_step h₁ with ⟨sc₃, e₂, e₃⟩
  rw [decodeOps] at h₂
  bind_step h₂ with ⟨ts, -, h₂⟩
  bind_step h₂ with ⟨rs, f₁, h₂⟩
  split at h₂
  · cases h₂
  bind_step h₂ with ⟨regs, f₂, h₂⟩
  bind_step h₂ with ⟨os, f₃, h₂⟩
  cases h₂
  obtain ⟨k₁, n₁⟩ := define_holds e₁ f₁ hsc hnd
  obtain ⟨k₂, n₂⟩ := hreg e₂ f₂ k₁ n₁
  obtain ⟨k₃, n₃⟩ := hos e₃ f₃ k₂ n₂
  simp only [Operation.scopeDefs, List.append_assoc] at k₃ n₃ ⊢
  exact ⟨k₃, n₃⟩

/-- The first pass adds nothing for no regions. -/
theorem adds_regions_nil : Adds (d := d) defineRegions decodeRegions Region.scopeDefs [] := by
  intro sc sc' sc₂ g L x h₁ h₂ hsc hnd
  rw [defineRegions] at h₁
  rw [decodeRegions] at h₂
  cases h₁
  cases h₂
  simpa [Region.scopeDefs] using ⟨hsc, hnd⟩

/-- The first pass adds a region's blocks' definitions, then those of the
regions after it. -/
theorem adds_regions_cons {bs : List SBlock} {srs : List SRegion}
    (hb : Adds (d := d) defineBlocks decodeBlocks Block.scopeDefs bs)
    (hrs : Adds (d := d) defineRegions decodeRegions Region.scopeDefs srs) :
    Adds (d := d) defineRegions decodeRegions Region.scopeDefs (⟨bs⟩ :: srs) := by
  intro sc sc' sc₂ g L x h₁ h₂ hsc hnd
  rw [defineRegions] at h₁
  bind_step h₁ with ⟨sc₁, e₁, e₂⟩
  rw [decodeRegions] at h₂
  bind_step h₂ with ⟨blocks, f₁, h₂⟩
  bind_step h₂ with ⟨rs, f₂, h₂⟩
  cases h₂
  obtain ⟨k₁, n₁⟩ := hb e₁ f₁ hsc hnd
  obtain ⟨k₂, n₂⟩ := hrs e₂ f₂ k₁ n₁
  simp only [Region.scopeDefs, List.append_assoc] at k₂ n₂ ⊢
  exact ⟨k₂, n₂⟩

mutual
/-- The first pass over blocks, at any depth. -/
theorem SBlock.adds :
    ∀ sbs : List SBlock, Adds (d := d) defineBlocks decodeBlocks Block.scopeDefs sbs
  | [] => adds_blocks_nil
  | ⟨_, _, ops⟩ :: sbs => adds_blocks_cons (SOp.adds ops) (SBlock.adds sbs)

/-- The first pass over ops, at any depth. -/
theorem SOp.adds : ∀ sos : List SOp, Adds (d := d) defineOps decodeOps Operation.scopeDefs sos
  | [] => adds_ops_nil
  | ⟨_, _, _, _, _, _, regions, _⟩ :: sos => adds_ops_cons (SRegion.adds regions) (SOp.adds sos)

/-- The first pass over regions, at any depth. -/
theorem SRegion.adds : ∀ srs : List SRegion,
    Adds (d := d) defineRegions decodeRegions Region.scopeDefs srs
  | [] => adds_regions_nil
  | ⟨bs⟩ :: srs => adds_regions_cons (SBlock.adds bs) (SRegion.adds srs)
end

end Fir.Text
