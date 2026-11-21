import Fir.Validation.Scope

/-!
Where a block of a function sits: in its body, or in a region of an op of
one of its blocks, at any depth. The rules of validation take each op of a
function once, as an op of its body or as an op inside a region, and these
lemmas say that the two cover every block.
-/

namespace Fir

variable {d : Dialect}

/-- The block `b` is a block of a region of an op of a block of `all`. -/
def Block.InRegionOf (all : List (Block d)) (b : Block d) : Prop :=
  ∃ b₀ ∈ all, ∃ o ∈ b₀.body, ∃ r ∈ o.regions, b ∈ r.blocks

theorem Block.InRegionOf.mono {all all' : List (Block d)} {b : Block d}
    (h : ∀ x ∈ all, x ∈ all') : Block.InRegionOf all b → Block.InRegionOf all' b
  | ⟨b₀, hb₀, rest⟩ => ⟨b₀, h b₀ hb₀, rest⟩

section

/-- Each block of a list is among its blocks at any depth. -/
theorem Block.mem_allBlocks {b : Block d} :
    ∀ {bs : List (Block d)}, b ∈ bs → b ∈ Block.allBlocks bs
  | ⟨_, _, _⟩ :: _, h => by
    rw [Block.allBlocks]
    rcases List.mem_cons.1 h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (Block.mem_allBlocks h))

mutual
/-- A block of these regions, at any depth, is a block of one of them, or of
a region of an op of one of their blocks. -/
theorem Region.mem_allBlocks_cases : ∀ {rs : List (Region d)} {b : Block d},
    b ∈ Region.allBlocks rs → (∃ r ∈ rs, b ∈ r.blocks) ∨ Block.InRegionOf (Region.allBlocks rs) b
  | [], _, h => by simp [Region.allBlocks] at h
  | ⟨k, bs⟩ :: rs, b, h => by
    have hsub₁ : ∀ x ∈ Block.allBlocks bs, x ∈ Region.allBlocks (⟨k, bs⟩ :: rs) := fun x hx => by
      rw [Region.allBlocks]; exact List.mem_append_left _ hx
    have hsub₂ : ∀ x ∈ Region.allBlocks rs, x ∈ Region.allBlocks (⟨k, bs⟩ :: rs) := fun x hx => by
      rw [Region.allBlocks]; exact List.mem_append_right _ hx
    rw [Region.allBlocks] at h
    rcases List.mem_append.1 h with h | h
    · rcases Block.mem_allBlocks_cases h with h | h
      · exact .inl ⟨_, List.mem_cons_self, h⟩
      · exact .inr (h.mono hsub₁)
    · rcases Region.mem_allBlocks_cases h with ⟨r, hr, hb⟩ | h
      · exact .inl ⟨r, List.mem_cons_of_mem _ hr, hb⟩
      · exact .inr (h.mono hsub₂)

/-- A block of these blocks at any depth is one of them, or a block of a
region of an op of one of them, at any depth. -/
theorem Block.mem_allBlocks_cases : ∀ {bs : List (Block d)} {b : Block d},
    b ∈ Block.allBlocks bs → b ∈ bs ∨ Block.InRegionOf (Block.allBlocks bs) b
  | [], _, h => by simp [Block.allBlocks] at h
  | ⟨l, ps, body⟩ :: bs, b, h => by
    have hsub₁ : ∀ x ∈ Operation.regionBlocks body,
        x ∈ Block.allBlocks (⟨l, ps, body⟩ :: bs) := fun x hx => by
      rw [Block.allBlocks]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hx)
    have hsub₂ : ∀ x ∈ Block.allBlocks bs, x ∈ Block.allBlocks (⟨l, ps, body⟩ :: bs) :=
      fun x hx => by
        rw [Block.allBlocks]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hx)
    have hself : ⟨l, ps, body⟩ ∈ Block.allBlocks (⟨l, ps, body⟩ :: bs) := by
      rw [Block.allBlocks]; exact List.mem_cons_self
    rw [Block.allBlocks] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact .inl List.mem_cons_self
    rcases List.mem_append.1 h with h | h
    · rcases Operation.mem_regionBlocks_cases h with ⟨o, ho, r, hr, hb⟩ | h
      · exact .inr ⟨_, hself, o, ho, r, hr, hb⟩
      · exact .inr (h.mono hsub₁)
    · rcases Block.mem_allBlocks_cases h with h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · exact .inr (h.mono hsub₂)

/-- A block of the regions of these ops, at any depth, is a block of a
region of one of them, or of a region of an op of a block below them. -/
theorem Operation.mem_regionBlocks_cases : ∀ {os : List (Operation d)} {b : Block d},
    b ∈ Operation.regionBlocks os → (∃ o ∈ os, ∃ r ∈ o.regions, b ∈ r.blocks) ∨
      Block.InRegionOf (Operation.regionBlocks os) b
  | [], _, h => by simp [Operation.regionBlocks] at h
  | ⟨rs', op, xs, ss, regions, loc⟩ :: os, b, h => by
    have hsub₁ : ∀ x ∈ Region.allBlocks regions,
        x ∈ Operation.regionBlocks (⟨rs', op, xs, ss, regions, loc⟩ :: os) := fun x hx => by
      rw [Operation.regionBlocks]; exact List.mem_append_left _ hx
    have hsub₂ : ∀ x ∈ Operation.regionBlocks os,
        x ∈ Operation.regionBlocks (⟨rs', op, xs, ss, regions, loc⟩ :: os) := fun x hx => by
      rw [Operation.regionBlocks]; exact List.mem_append_right _ hx
    rw [Operation.regionBlocks] at h
    rcases List.mem_append.1 h with h | h
    · rcases Region.mem_allBlocks_cases h with ⟨r, hr, hb⟩ | h
      · exact .inl ⟨_, List.mem_cons_self, r, hr, hb⟩
      · exact .inr (h.mono hsub₁)
    · rcases Operation.mem_regionBlocks_cases h with ⟨o, ho, r, hr, hb⟩ | h
      · exact .inl ⟨o, List.mem_cons_of_mem _ ho, r, hr, hb⟩
      · exact .inr (h.mono hsub₂)
end

end

/-- A block of a function at any depth is a block of its body, or a block of
a region of an op of one of its blocks at any depth. -/
theorem Func.mem_allBlocks_cases {f : Func d} {b : Block d} (h : b ∈ f.allBlocks) :
    b ∈ f.blocks ∨ Block.InRegionOf f.allBlocks b :=
  Block.mem_allBlocks_cases h

end Fir
