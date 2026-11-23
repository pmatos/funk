import Fir.Core.Event
import Fir.Execution.TraceWorldRefine
import Fir.Execution.TraceFinite

/-!
# The core's traced external-call rule

The run hands a call to an external declaration to the dialect's
external-call rule (`Fir.Execution.ExtCall`, the human's ruling of
2026-11-21 on #239, Q1). In the traced layer, where the world answers, the
core's rule for a call of the declaration `g` on the arguments `args` for
results of the types `rs` runs in three parts, from the traced state `s`:

* The call lets escape what it reaches (`TraceState.escapeCall`): the
  allocations of its pointer arguments, and every allocation that an
  escaped allocation points into, in an order fixed by positions (the
  human's ruling of 2026-11-20 on #239).
* It shows its event, `call g args seen`, as the world sees it from the
  traced state it has reached (`Event.ofCall`), and asks the world
  (`TraceM.ask`). Every world counts, so the world may give any reply and
  take any actions on escaped memory that it can take.
* The reply's values are the call's results, read back in the traced state
  that the world's actions leave (`TraceState.fromWorldPtr`). The world
  gives values of the call's result types, in order, and names only
  allocations of its escaped list, each in its own memory. A reply that
  does not is one the world cannot give, as an action that it cannot take
  is (`WorldAct.apply`): the call has no outcome for it.

The memory numbered `n` is `μ n`, as for what the world sees. The core
names its memories by number, and a sum numbers its memories as its base
does, so #239's next stage is expected to install the rule with `μ` the
names that the run gives the core's memories, with no new parameter of
the traced semantics; that stage checks it against the theorems, which
take `μ` apart from those names.

Its laws, in the forms the traced layer's theorems use:

* _It has an outcome_ from every traced state: the world can answer with a
  poison of each result type and no action.
* _Its results have the call's result types._
* _It has finitely many outcomes, given the world's answers_
  (`TraceFinitelyMany`): the world's answer fixes the outcome.
* _It is monotone when both calls let escape the same allocations, in the
  same order_: on arguments that refine others, from traced states that
  refine others, when the two escaped lists after the calls are equal,
  each way the call may end on the others is allowed by a way it may end on
  the first, with the same reply and the same actions. The lists must be
  equal as lists, the same allocations in the same order, since the world
  names each by its place (the human's ruling of 2026-11-22 on #239, Q6).
  Without that condition the rule is not monotone: where the source has
  poison and the target a pointer, the target lets escape an allocation
  that the source does not, and the world may write into it (Q4).

This rule is not yet the core's. The core's traced semantics still runs an
external call by its rule with memory, UB, lifted (`Fir.Core.Trace`), and
validation rejects a call to a declaration. #239's next stage makes it the
core's rule, with the conditions of Q4 to Q6 on the theorems that use it.
-/

namespace Fir.Core

open Memory

variable {N : Type} [DecidableEq N] {w : N → Nat} (μ : Nat → N)

/-- Poison, a value of every core type. -/
def Ty.poison : (t : Ty) → ⟦t⟧
  | .int _ => PoisonOr.poison
  | .float _ _ => PoisonOr.poison
  | .ptr _ => PoisonOr.poison

/-- The world's reply `reply`, read back in the traced state `s` as the
results of a call for results of the types `rs`: its values, each pointer
read back by its handle, when they have the types `rs` and each pointer can
be read back; none otherwise. -/
def readReply (s : TraceState N w) (rs : List Ty) (reply : Reply) :
    Option (List (DVal CoreDialect)) :=
  if reply.map (·.1) = rs ∧
      (HasPtrs.ptrs reply).all (fun q => (s.fromWorldPtr μ q.1 q.2).isSome) = true then
    some (HasPtrs.map (s.fromWorldPtr μ) reply)
  else none

/-- Reading back the world's reply as the results of a call for results of
the types `rs`: no act, the traced state unchanged, and no outcome when the
reply cannot be read back. -/
def TraceM.reply {A : Type} (rs : List Ty) (reply : Reply) :
    TraceM A (TraceState N w) (List (DVal CoreDialect)) :=
  fun s e => ∃ vs, readReply μ s rs reply = some vs ∧ e = .ok (vs, [], s)

/-- The core's traced external-call rule: a call of the declaration `g` on
the arguments `args` for results of the types `rs` lets escape what it
reaches, shows its event from there, asks the world, and reads back its
reply as the call's results. -/
def traceExtCall (g : Name) (args : List (DVal CoreDialect)) (rs : List Ty) :
    TraceM (Act Event (Reply × List WorldAct)) (TraceState N w) (List (DVal CoreDialect)) :=
  fun s =>
    let s₁ := s.escapeCall μ (HasPtrs.ptrs args)
    (TraceM.ask μ (Event.ofCall μ s₁ g args) >>= TraceM.reply μ rs) s₁

/-- The ways the core's traced external-call rule may end: with the results
that the world's reply reads back as, in the traced state its actions
leave, after the one act of the call's event with the reply and the
actions. -/
theorem traceExtCall_iff {g : Name} {args : List (DVal CoreDialect)} {rs : List Ty}
    {s : TraceState N w} {e : TraceEnd (Act Event (Reply × List WorldAct)) (TraceState N w) _} :
    traceExtCall μ g args rs s e ↔ ∃ reply ws s' vs,
      WorldAct.applyAll μ ws (s.escapeCall μ (HasPtrs.ptrs args)) = some s' ∧
      readReply μ s' rs reply = some vs ∧
      e = .ok (vs, [⟨Event.ofCall μ (s.escapeCall μ (HasPtrs.ptrs args)) g args, (reply, ws)⟩], s') := by
  unfold traceExtCall
  rw [TraceM.bind_apply]
  constructor
  · rintro (⟨a, t, s', e', ⟨a', ws, s'', hws, he⟩, ⟨vs, hr, rfl⟩, rfl⟩ | ⟨r, t, ⟨_, _, _, _, he⟩, -⟩)
    · simp only [Except.ok.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact ⟨_, ws, _, vs, hws, hr, rfl⟩
    · cases he
  · rintro ⟨reply, ws, s', vs, hws, hr, rfl⟩
    exact .inl ⟨reply, [⟨Event.ofCall μ (s.escapeCall μ (HasPtrs.ptrs args)) g args, (reply, ws)⟩],
      s', .ok (vs, [], s'), ⟨reply, ws, s', hws, rfl⟩, ⟨vs, hr, rfl⟩, by simp [TraceEnd.after]⟩

/-! # Its laws -/

/-- A poison of each type holds no pointer. -/
theorem ptrs_poisons : ∀ rs : List Ty,
    HasPtrs.ptrs (rs.map fun t => (⟨t, Ty.poison t⟩ : DVal CoreDialect)) = []
  | [] => rfl
  | .int _ :: rs | .float _ _ :: rs | .ptr _ :: rs => ptrs_poisons rs

/-- The core's traced external-call rule has an outcome from every traced
state: the world can answer with a poison of each result type and no
action. -/
theorem traceExtCall_exists (g : Name) (args : List (DVal CoreDialect)) (rs : List Ty)
    (s : TraceState N w) : ∃ vs t s', traceExtCall μ g args rs s (.ok (vs, t, s')) := by
  let s₁ := s.escapeCall μ (HasPtrs.ptrs args)
  let reply : Reply := rs.map fun t => ⟨t, Ty.poison t⟩
  have hr : readReply μ s₁ rs reply = some (HasPtrs.map (s₁.fromWorldPtr μ) reply) := by
    have h1 : reply.map (·.1) = rs := by
      simp only [reply, List.map_map]
      exact List.map_id' rs
    have h2 : (HasPtrs.ptrs reply).all (fun q => (s₁.fromWorldPtr μ q.1 q.2).isSome) = true := by
      rw [show HasPtrs.ptrs reply = [] from ptrs_poisons rs]
      rfl
    unfold readReply
    simp only [h1, h2, and_self, ↓reduceIte]
  exact ⟨_, _, _, (traceExtCall_iff μ).2 ⟨reply, [], s₁, _, rfl, hr, rfl⟩⟩

/-- The core's traced external-call rule gives values of the call's result
types, in order. -/
theorem traceExtCall_types {g : Name} {args : List (DVal CoreDialect)} {rs : List Ty}
    {s s' : TraceState N w} {vs : List (DVal CoreDialect)} {t : List (Act Event (Reply × List WorldAct))}
    (h : traceExtCall μ g args rs s (.ok (vs, t, s'))) : vs.map (·.1) = rs := by
  obtain ⟨reply, ws, s'', vs', -, hr, he⟩ := (traceExtCall_iff μ).1 h
  simp only [Except.ok.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, -, -⟩ := he
  unfold readReply at hr
  split at hr
  · rename_i hc
    cases hr
    rw [← hc.1]
    show (reply.map (HasPtrs.map _)).map (·.1) = _
    rw [List.map_map]
    rfl
  · cases hr

/-- The core's traced external-call rule has finitely many outcomes, given
the world's answers: the world's answer to its one event fixes the reply,
the actions, and so the outcome. -/
theorem traceExtCall_finite (g : Name) (args : List (DVal CoreDialect)) (rs : List Ty) :
    TraceFinitelyMany (traceExtCall (w := w) μ g args rs) := by
  intro s ans
  let s₁ := s.escapeCall μ (HasPtrs.ptrs args)
  refine ⟨match ans 0 with
    | some (reply, ws) => ((WorldAct.applyAll μ ws s₁).bind fun s' => (readReply μ s' rs reply).map
        fun vs => (vs, [⟨Event.ofCall μ s₁ g args, (reply, ws)⟩], s')).toList
    | none => [], fun vs t s' h hag => ?_⟩
  obtain ⟨reply, ws, s'', vs', hws, hr, he⟩ := (traceExtCall_iff μ).1 h
  simp only [Except.ok.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  have h0 : ans 0 = some (reply, ws) := hag 0 _ rfl
  simp only [h0]
  show _ ∈ ((WorldAct.applyAll μ ws s₁).bind _).toList
  rw [hws]
  simp [hr, s₁]

/-- The core's traced external-call rule is monotone when both calls let
escape the same allocations, in the same order: on arguments that refine
others, from traced states that refine others, when the escaped lists after
the two calls are equal, each way the call may end on the others is allowed
by a way it may end on the first, which shows the same reply and actions
for an event that the other's refines, and the same results. -/
theorem traceExtCall_isRefinedBy {args args' : List (DVal CoreDialect)} (ha : args ⊑ args')
    {s s' : TraceState N w} (hS : s ⊑ s')
    (hesc : (s.escapeCall μ (HasPtrs.ptrs args)).escaped =
      (s'.escapeCall μ (HasPtrs.ptrs args')).escaped) (g : Name) (rs : List Ty) :
    ∀ e', traceExtCall μ g args' rs s' e' → ∃ e, traceExtCall μ g args rs s e ∧
      TraceEnd.Allows (fun vs vs' : List (DVal CoreDialect) => vs ⊑ vs') e e' := by
  intro e' h
  obtain ⟨reply, ws, t', vs, hws, hr, rfl⟩ := (traceExtCall_iff μ).1 h
  have hS₁ : s.escapeCall μ (HasPtrs.ptrs args) ⊑ s'.escapeCall μ (HasPtrs.ptrs args') :=
    ⟨by rw [TraceState.escapeCall_mem, TraceState.escapeCall_mem]; exact hS.1, hesc⟩
  obtain ⟨t, ht, htt⟩ := WorldAct.applyAll_isRefinedBy μ ws hS₁ hws
  have hr' : readReply μ t rs reply = some vs := by
    unfold readReply at hr ⊢
    rwa [TraceState.fromWorldPtr_congr μ htt.2]
  refine ⟨_, (traceExtCall_iff μ).2 ⟨reply, ws, t, vs, ht, hr', rfl⟩,
    List.isRefinedBy_refl (fun (v : DVal CoreDialect) => (⟨rfl, Ty.isRefinedBy_refl v.2⟩ : v ⊑ v)) _,
    ⟨⟨Event.ofCall_isRefinedBy μ hS₁ g ha, rfl⟩, trivial⟩, htt⟩

end Fir.Core
