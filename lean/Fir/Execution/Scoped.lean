import Fir.Execution.Environment
import Fir.Validation.Rules

/-!
# The values in scope at each op

A run that jumps reaches a block with an environment that another block
built. What it may find there follows from validation: before the op at
index i of the block labelled l, the run's environment holds, for each
value in scope at that op, a value of the type that the function gives
it. Every operand of the op, and every value that it passes to a
successor, is in scope, so the run finds each of them with its type.

Three steps keep the invariant, each by the rules of scope and dominance:

* _At the entry: only the parameters are in scope at the first op of the
  entry block._ No block dominates the entry but itself, and the entry
  block declares no arguments. The run starts with each parameter bound to
  its argument.
* _From an op to the next: a value in scope at the next op is a result of
  this op, or was in scope at this op._ The run has just bound the
  results of this op.
* _Along a jump: a value in scope at the first op of a jump's target is an
  argument of the target, or was in scope at the op that jumps._ The jump
  has just bound the target's arguments. A value defined in another block
  that dominates the target is defined in a block that dominates every
  block that jumps to it, so the value was in scope at the terminator that
  jumped, unless it is a result of that terminator. The interpreter binds
  no result of a terminator, so this asks that a terminator that jumps has
  none, as no core terminator has.

A step binds its names in front of the environment. A lookup of a name
that it binds finds the new value, and a lookup of any other name finds
what it found before, so the proof needs no fact that the new names are
new.
-/

namespace Fir

section

variable {d : Dialect}

/-- Two members of a list on which `g` has no repeated value are equal when
`g` gives them the same value. -/
theorem eq_of_nodup_map {α β : Type} {g : α → β} {a b : α} :
    ∀ {l : List α}, (l.map g).Nodup → a ∈ l → b ∈ l → g a = g b → a = b
  | c :: l, hnd, ha, hb, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · rfl
      · exact absurd (h ▸ List.mem_map_of_mem hb') hnd.1
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd (h.symm ▸ List.mem_map_of_mem ha') hnd.1
      · exact eq_of_nodup_map hnd.2 ha' hb' h

/-- Each block of a list is among its blocks at any depth. -/
theorem Block.mem_allBlocks {b : Block d} :
    ∀ {bs : List (Block d)}, b ∈ bs → b ∈ Block.allBlocks bs
  | ⟨_, _, _⟩ :: _, h => by
    rw [Block.allBlocks]
    rcases List.mem_cons.1 h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (Block.mem_allBlocks h))

/-- The arguments of a block of a function are among its definitions. -/
theorem Func.mem_defs_arg {f : Func d} {b : Block d} (hb : b ∈ f.blocks) {p : Name × d.Ty}
    (hp : p ∈ b.params) : p ∈ f.defs := by
  simp only [Func.defs, List.mem_append, List.mem_flatMap]
  exact .inr ⟨b, Block.mem_allBlocks hb, by simp [Block.defs, hp]⟩

/-- The results of an op of a block of a function are among its
definitions. -/
theorem Func.mem_defs_result {f : Func d} {b : Block d} (hb : b ∈ f.blocks)
    {o : Operation d} (ho : o ∈ b.body) {p : Name × d.Ty} (hp : p ∈ o.results) :
    p ∈ f.defs := by
  simp only [Func.defs, List.mem_append, List.mem_flatMap]
  exact .inr ⟨b, Block.mem_allBlocks hb, by
    simp only [Block.defs, List.mem_append, List.mem_flatMap]
    exact .inr ⟨o, ho, hp⟩⟩

/-- The block that a function finds by a label is one of its blocks, with
that label. -/
theorem Func.block?_some {f : Func d} {l : Name} {b : Block d} (h : f.block? l = some b) :
    b ∈ f.blocks ∧ b.label = l :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- A block that dominates a block other than itself dominates every block
that jumps to it. -/
theorem Func.dominates_of_edge {f : Func d} {a l l' : Name} (h : f.Dominates a l')
    (ha : a ≠ l') (he : f.Edge l l') : f.Dominates a l := by
  by_cases hal : a = l
  · exact .inl hal
  · exact .inr fun hr => (h.resolve_left ha) (.step hr he (Ne.symm ha))

variable [DialectSignature d] [DialectValidation d] {ctx : ModuleContext d} {f : Func d}

/-- In a valid function, two of its blocks with one label are one block. -/
theorem Func.Valid.block_eq (hv : f.Valid ctx) {b b' : Block d} (hb : b ∈ f.blocks)
    (hb' : b' ∈ f.blocks) (h : b.label = b'.label) : b = b' :=
  eq_of_nodup_map hv.labelsUnique hb hb' h

/-- Only the parameters are in scope at the first op of the entry block. -/
theorem Func.mem_params_of_inScope (hv : f.Valid ctx) {e : Block d}
    (he : f.blocks.head? = some e) (hep : e.params = []) {x : Name}
    (hx : f.InScope x e.label 0) : x ∈ f.params.map (·.1) := by
  have hmem : e ∈ f.blocks := List.mem_of_mem_head? he
  have hentry : f.entryLabel? = some e.label := by simp [Func.entryLabel?, he]
  have hdom : ∀ a, f.Dominates a e.label → a = e.label := fun a h =>
    h.elim id fun h' => Classical.byContradiction fun ha =>
      h' (Func.ReachesAvoiding.entry hentry (Ne.symm ha))
  obtain ⟨⟨s, hs⟩, hall⟩ := hx
  have hd := hall s hs
  cases s with
  | param => exact hs
  | arg a =>
    obtain ⟨b, hb, hl, hxb⟩ := hs
    have hbe := hv.block_eq hb hmem (hl.trans (hdom a hd))
    subst hbe
    rw [hep] at hxb
    cases hxb
  | result a j =>
    rcases hd with ⟨_, hj⟩ | ⟨ha, hd⟩
    · cases hj
    · exact absurd (hdom a hd) ha

/-- A value in scope at the op after the op at index `i` of a block is a
result of that op, or was in scope at it. -/
theorem Func.inScope_of_next (hv : f.Valid ctx) {b : Block d} (hb : b ∈ f.blocks) {i : Nat}
    (hi : i < b.body.length) {x : Name} (hx : f.InScope x b.label (i + 1))
    (hnot : x ∉ b.body[i].results.map (·.1)) : f.InScope x b.label i := by
  refine ⟨hx.1, fun s hs => ?_⟩
  have hd := hx.2 s hs
  cases s with
  | param => trivial
  | arg a => exact hd
  | result a j =>
    rcases hd with ⟨ha, hj⟩ | hd
    · refine .inl ⟨ha, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) fun hji => ?_⟩
      subst hji
      obtain ⟨b', hb', hl, o, ho, hxo⟩ := hs
      have hbb := hv.block_eq hb' hb (hl.trans ha)
      subst hbb
      rw [List.getElem?_eq_getElem hi] at ho
      cases ho
      exact hnot hxo
    · exact .inr hd

/-- A value in scope at the first op of the block that a terminator jumps
to is an argument of that block, or was in scope at the terminator, when
the terminator has no results. -/
theorem Func.inScope_of_jump (hv : f.Valid ctx) {b tgt : Block d} (hb : b ∈ f.blocks)
    (htgt : tgt ∈ f.blocks) {i : Nat} {o : Operation d} (ho : b.body[i]? = some o)
    (hlast : i + 1 = b.body.length) (hres : o.results = []) {s : Succ} (hs : s ∈ o.succs)
    (hl : tgt.label = s.label) {x : Name} (hx : f.InScope x tgt.label 0)
    (hnot : x ∉ tgt.params.map (·.1)) : f.InScope x b.label i := by
  have hedge : f.Edge b.label tgt.label :=
    ⟨b, hb, rfl, hl ▸ List.mem_flatMap.2 ⟨o, List.mem_of_getElem? ho, List.mem_map_of_mem hs⟩⟩
  refine ⟨hx.1, fun s' hs' => ?_⟩
  have hd := hx.2 s' hs'
  cases s' with
  | param => trivial
  | arg a =>
    refine Func.dominates_of_edge hd (fun ha => ?_) hedge
    obtain ⟨b', hb', hl', hxb⟩ := hs'
    have hbb := hv.block_eq hb' htgt (hl'.trans ha)
    subst hbb
    exact hnot hxb
  | result a j =>
    rcases hd with ⟨_, hj⟩ | ⟨ha, hd⟩
    · cases hj
    have hdl := Func.dominates_of_edge hd ha hedge
    by_cases hab : a = b.label
    · refine .inl ⟨hab, ?_⟩
      obtain ⟨b', hb', hl', o', ho', hxo⟩ := hs'
      have hbb := hv.block_eq hb' hb (hl'.trans hab)
      subst hbb
      have hj := (List.getElem?_eq_some_iff.1 ho').1
      refine Nat.lt_of_le_of_ne (by omega) fun hji => ?_
      subst hji
      rw [ho] at ho'
      cases ho'
      rw [hres] at hxo
      cases hxo
    · exact .inr ⟨hab, hdl⟩

end

section

variable {d : Dialect} [TyDenote d.Ty]

/-- The environment holds, for each value in scope at the op at index `i`
of the block labelled `l` of the function `f`, a value of the type that `f`
gives it. -/
def Env.Scoped (env : Env d) (f : Func d) (l : Name) (i : Nat) : Prop :=
  ∀ x, f.InScope x l i → ∃ dv, env.lookup x = some dv ∧ f.typeOf x = some dv.1

/-- Binding the names of `ps` to values of their types, where `f` gives
each its type, gives an environment that holds every value in scope at an
op, when the old one held each such value that `ps` does not name. -/
theorem Env.scoped_bind {env : Env d} {f : Func d} {l : Name} {i : Nat}
    {ps : List (Name × d.Ty)} {dvs : List (DVal d)} (ht : dvs.map (·.1) = ps.map (·.2))
    (hdef : ∀ p ∈ ps, f.typeOf p.1 = some p.2)
    (hold : ∀ x, f.InScope x l i → x ∉ ps.map (·.1) →
      ∃ dv, env.lookup x = some dv ∧ f.typeOf x = some dv.1) :
    Env.Scoped ((ps.map (·.1)).zip dvs ++ env) f l i := by
  have hlen : (ps.map (·.1)).length = dvs.length := by
    rw [List.length_map, ← List.length_map (f := (·.2)), ← ht, List.length_map]
  intro x hx
  by_cases hm : x ∈ ps.map (·.1)
  · have hz : x ∈ ((ps.map (·.1)).zip dvs).map (·.1) := by
      rw [List.map_fst_zip (Nat.le_of_eq hlen)]
      exact hm
    obtain ⟨dv, hl, hmz⟩ := lookup_of_mem hz
    exact ⟨dv, by rw [List.lookup_append, hl]; rfl, hdef _ (mem_zip_types ht hmz)⟩
  · have hz : x ∉ ((ps.map (·.1)).zip dvs).map (·.1) := by
      rw [List.map_fst_zip (Nat.le_of_eq hlen)]
      exact hm
    obtain ⟨dv, hl, hty⟩ := hold x hx hm
    exact ⟨dv, by rw [lookup_append_of_not_mem hz, hl], hty⟩

/-- The environment holds each of the values in scope. -/
theorem Env.Scoped.holds {env : Env d} {f : Func d} {l : Name} {i : Nat}
    (hold : env.Scoped f l i) {xs : List Name} (h : ∀ x ∈ xs, f.InScope x l i) :
    env.Holds f xs :=
  fun x hx => hold x (h x hx)

variable [DialectSignature d] [DialectValidation d] {ctx : ModuleContext d} {f : Func d}

/-- A run starts with the invariant at the entry block's first op: the
parameters, bound to arguments of their types. -/
theorem Env.scoped_params (hv : f.Valid ctx) {e : Block d} (he : f.blocks.head? = some e)
    (hep : e.params = []) (args : HVector toType (f.params.map (·.2))) :
    Env.Scoped ((f.params.map (·.1)).zip args.toDVals) f e.label 0 := by
  have h := Env.scoped_bind (env := []) (f := f) (l := e.label) (i := 0) (ps := f.params)
    (HVector.toDVals_types args)
    (fun p hp => Func.typeOf_of_mem hv.namesUnique (List.mem_append_left _ hp))
    (fun x hx hnot => absurd (Func.mem_params_of_inScope hv he hep hx) hnot)
  simpa using h

end

end Fir
