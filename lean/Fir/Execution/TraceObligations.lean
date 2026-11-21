import Fir.Execution.TraceDialect
import Fir.Execution.MemoryOpRefine

/-!
# Monotonicity in the traced layer

Refined arguments ask each op that runs by its own rule to be monotone
(`Fir.Execution.MemoryOpRefine`). For a dialect whose ops show events, the
obligation speaks of the op's semantics in the traced layer, and the
traced state it starts from may refine another:

* _Refined traced states_: one traced state refines another when its
  memories refine the other's and the same allocations escaped, in the same
  order, so the world names each by the same handle.
* _Refined marked traces_: a step refines a step, and an act refines an act
  whose event it refines with the same answer (`Fir.Execution.Trace`).
* _Monotone in the traced layer_: on operands that refine others, and from
  traced states that refine others, each way an op may end is allowed by a
  way it may end on those others. A result is allowed by a result that it
  refines, with acts that it refines one by one and a traced state that it
  refines. UB after the acts _t_ allows each way of ending that first shows
  acts refining _t_: as for whole runs, UB in the source allows only a
  target that first shows the source's events.

The traced layer of marked traces runs an op by its dialect's rule after a
step. The step and mapping each act to the act of a marked trace keep the
obligation, so an op monotone by its dialect's rule is monotone in the
traced layer of marked traces.

A dialect whose ops show no event runs its semantics with memory, lifted onto
the memories of the traced state (`DialectTrace.ofMem`). The lift keeps
what escaped and shows nothing, so an op monotone with memory is monotone
in the traced layer.
-/

namespace Fir

open Memory

variable {A B σ α β : Type}

/-! # Refined marked traces -/

/-- An element of a marked trace refined by another: a step by a step, an act
by an act that refines it. -/
def Step.IsRefinedBy [HRefinement A A] : Step A → Step A → Prop
  | .tick, .tick => True
  | .act a, .act b => a ⊑ b
  | _, _ => False

instance [HRefinement A A] : HRefinement (Step A) (Step A) := ⟨Step.IsRefinedBy⟩

/-- `l` is refined by a prefix of `l'`: the list `l'` first shows a list that
refines `l`, element by element. -/
def List.IsRefinedPrefix [HRefinement A A] (l l' : List A) : Prop :=
  ∃ m, l ⊑ m ∧ m <+: l'

section

variable [HRefinement A A]

/-- The empty list is refined by a prefix of every list. -/
theorem List.isRefinedPrefix_nil (l : List A) : List.IsRefinedPrefix [] l :=
  ⟨[], trivial, List.nil_prefix⟩

/-- A refined prefix stays one after both lists are preceded by lists that
refine element by element. -/
theorem List.IsRefinedPrefix.append_left {t t' l l' : List A} (ht : t ⊑ t')
    (h : List.IsRefinedPrefix l l') : List.IsRefinedPrefix (t ++ l) (t' ++ l') := by
  obtain ⟨m, hm, r, rfl⟩ := h
  exact ⟨t' ++ m, List.IsRefinedBy.append ht hm, r, by rw [List.append_assoc]⟩

/-- A refined prefix of a list is a refined prefix of every list that the
list starts. -/
theorem List.IsRefinedPrefix.append_right {l l' : List A} (h : List.IsRefinedPrefix l l')
    (r : List A) : List.IsRefinedPrefix l (l' ++ r) := by
  obtain ⟨m, hm, r', rfl⟩ := h
  exact ⟨m, hm, r' ++ r, by rw [List.append_assoc]⟩

/-- The acts of marked traces that refine each other refine each other. -/
theorem Step.actsOf_isRefinedBy : ∀ {mt mt' : List (Step A)}, mt ⊑ mt' →
    Step.actsOf mt ⊑ Step.actsOf mt'
  | [], [], _ => trivial
  | .tick :: l, .tick :: l', ⟨_, h⟩ => Step.actsOf_isRefinedBy (mt := l) (mt' := l') h
  | .act _ :: _, .act _ :: _, ⟨ha, h⟩ => ⟨ha, Step.actsOf_isRefinedBy h⟩
  | [], _ :: _, h | _ :: _, [], h => h.elim
  | .tick :: _, .act _ :: _, ⟨h, _⟩ | .act _ :: _, .tick :: _, ⟨h, _⟩ => h.elim

/-- Mapping each act to an act of a marked trace keeps refinement. -/
theorem Step.flatMap_act_isRefinedBy : ∀ {t t' : List A}, t ⊑ t' →
    t.flatMap (fun a => [Step.act a]) ⊑ t'.flatMap (fun a => [Step.act a])
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨ha, h⟩ => ⟨ha, Step.flatMap_act_isRefinedBy h⟩
  | [], _ :: _, h | _ :: _, [], h => h.elim

/-- The acts of a marked trace refined by a prefix of another are refined by a
prefix of its acts. -/
theorem Step.actsOf_isRefinedPrefix {mt mt' : List (Step A)} (h : List.IsRefinedPrefix mt mt') :
    List.IsRefinedPrefix (Step.actsOf mt) (Step.actsOf mt') := by
  obtain ⟨m, hm, r, rfl⟩ := h
  refine ⟨Step.actsOf m, Step.actsOf_isRefinedBy hm, Step.actsOf r, ?_⟩
  simp [Step.actsOf]

/-- Mapping each act to an act of a marked trace keeps a refined prefix. -/
theorem Step.flatMap_act_isRefinedPrefix {t t' : List A} (h : List.IsRefinedPrefix t t') :
    List.IsRefinedPrefix (t.flatMap fun a => [Step.act a]) (t'.flatMap fun a => [Step.act a]) := by
  obtain ⟨m, hm, r, rfl⟩ := h
  exact ⟨_, Step.flatMap_act_isRefinedBy hm, r.flatMap fun a => [Step.act a], by simp⟩

end

/-! # Refined traced states -/

section

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

/-- A traced state refined by another: the other's memories refine its own,
and the same allocations escaped, in the same order. -/
instance : HRefinement (TraceState Mem unit) (TraceState Mem unit) :=
  ⟨fun s s' => s.mem ⊑ s'.mem ∧ s.escaped = s'.escaped⟩

/-- A traced state refines itself. -/
theorem TraceState.isRefinedBy_refl (s : TraceState Mem unit) : s ⊑ s :=
  ⟨Memories.isRefinedBy_refl _, rfl⟩

/-- Entering a frame keeps refinement of traced states. -/
theorem TraceState.IsRefinedBy.enter {s s' : TraceState Mem unit} (h : s ⊑ s') :
    ({ s with mem := s.mem.enter } : TraceState Mem unit) ⊑ { s' with mem := s'.mem.enter } :=
  ⟨h.1.enter, h.2⟩

/-- Leaving a frame keeps refinement of traced states. -/
theorem TraceState.IsRefinedBy.exit {s s' : TraceState Mem unit} (h : s ⊑ s') :
    ({ s with mem := s.mem.exit } : TraceState Mem unit) ⊑ { s' with mem := s'.mem.exit } :=
  ⟨h.1.exit, h.2⟩

end

/-! # Ways of ending that allow others -/

/-- The trace that a way of ending shows. -/
def TraceEnd.trace : TraceEnd A σ α → List A
  | .ok (_, t, _) => t
  | .error (_, t) => t

/-- After a trace, a way of ending shows that trace first. -/
theorem TraceEnd.trace_after (t : List A) (e : TraceEnd A σ α) : (e.after t).trace = t ++ e.trace := by
  cases e <;> rfl

section

variable [HRefinement A A] [HRefinement σ σ]

/-- A way of ending of the source allows a way of ending of the target: a
result allows a result related to it by `r`, with acts that refine its acts
one by one and a state that refines its state; UB after the acts `t` allows
each way of ending that first shows acts refining `t`. -/
def TraceEnd.Allows (r : α → β → Prop) : TraceEnd A σ α → TraceEnd A σ β → Prop
  | .ok (a, t, s), .ok (b, t', s') => r a b ∧ t ⊑ t' ∧ s ⊑ s'
  | .error (_, t), e' => List.IsRefinedPrefix t e'.trace
  | .ok _, .error _ => False

/-- UB that shows no act allows every way of ending. -/
theorem TraceEnd.Allows.of_ub {r : α → β → Prop} (reason : String) (e' : TraceEnd A σ β) :
    TraceEnd.Allows r (.error (reason, [])) e' :=
  List.isRefinedPrefix_nil _

/-- A way of ending that allows another still does after traces that refine
each other. -/
theorem TraceEnd.Allows.after {r : α → β → Prop} {t t' : List A} (ht : t ⊑ t') :
    ∀ {e : TraceEnd A σ α} {e' : TraceEnd A σ β}, TraceEnd.Allows r e e' →
      TraceEnd.Allows r (e.after t) (e'.after t')
  | .ok _, .ok _, h => ⟨h.1, List.IsRefinedBy.append ht h.2.1, h.2.2⟩
  | .error _, e', h => by
    show List.IsRefinedPrefix _ (e'.after t').trace
    rw [TraceEnd.trace_after]
    exact h.append_left ht
  | .ok _, .error _, h => h.elim

/-- A traced computation `c'` refines `c`, by `r` on what they give: from
traced states that refine others, each way `c'` may end is allowed by a way
`c` may end from those others. -/
def TraceRefinedBy (r : α → β → Prop) (c : TraceM A σ α) (c' : TraceM A σ β) : Prop :=
  ∀ s s', s ⊑ s' → ∀ e', c' s' e' → ∃ e, c s e ∧ TraceEnd.Allows r e e'

end

/-! # The obligation -/

section

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [TyRefinement d.Ty]
  [HRefinement B B] [HRefinement σ σ]

/-- In a semantics in the traced layer, the op is monotone: on operands that
refine others, what it runs by its own rule refines what it runs on those
others, from traced states that refine others. -/
def OpTraceMonotone [DialectDenote d (TraceM B σ)] (op : d.Op) : Prop :=
  ∀ args args' : HVector toType (sig op), args.Forall₂ TyRefinement.IsRefinedBy args' →
    (isTerminator op = false → TraceRefinedBy (HVector.Forall₂ TyRefinement.IsRefinedBy)
        (DialectDenote.denote (m := TraceM B σ) op args)
        (DialectDenote.denote (m := TraceM B σ) op args')) ∧
      (isTerminator op = true → TraceRefinedBy Eq (DialectDenote.exit (m := TraceM B σ) op args)
        (DialectDenote.exit (m := TraceM B σ) op args'))

variable [DialectCall d] [DialectDenote d (TraceM B σ)]

variable (B σ) in
/-- Every op of `os` that runs by its own rule, a terminator or an op with no
callee, is monotone in the traced layer. -/
def TraceMonotoneOps (os : List (Operation d)) : Prop :=
  ∀ o ∈ os, isTerminator o.op = true ∨ callee? o.op = none → OpTraceMonotone (B := B) (σ := σ) o.op

variable (B σ) in
/-- Every op of the function `f` that runs by its own rule is monotone in the
traced layer. -/
def Func.TraceOpsMonotone (f : Func d) : Prop :=
  ∀ b ∈ f.blocks, TraceMonotoneOps B σ b.body

variable [DecidableEq d.Ty]

/-- A run of `f` starts at the ops of one of its blocks. -/
theorem Func.TraceOpsMonotone.enter {f : Func d} (hf : f.TraceOpsMonotone B σ)
    {dvs : List (DVal d)} {p : List (Operation d) × Env d} (hen : f.enter dvs = .ok p) :
    TraceMonotoneOps B σ p.1 := by
  obtain ⟨e, he, -, -, rfl⟩ := Func.enter_eq_ok hen
  exact hf e (List.mem_of_mem_head? he)

/-- A jump of `f` goes to the ops of one of its blocks. -/
theorem Func.TraceOpsMonotone.jump {f : Func d} (hf : f.TraceOpsMonotone B σ) {env : Env d}
    {succs : List Succ} {i : Nat} {b : Block d} {env₁ : Env d}
    (hj : f.jump env succs i = .ok (b, env₁)) : TraceMonotoneOps B σ b.body := by
  obtain ⟨s, vs, -, hb, -⟩ := Func.jump_eq_ok hj
  exact hf b (Func.block?_some hb).1

end

end Fir
