import Fir.Execution.MemoryFree
import Fir.Execution.SummarySound
import Fir.Execution.MemoryReplace
import Fir.Execution.Replace

/-!
# Runs that touch no memory

Congruence in the callee with memory asks for a budget past which no run of
the new callee from any memories runs out of fuel unless it diverges (the
section on replacing a callee, with memory). A callee whose effects include
no memory read, write or allocation needs none: its runs do not depend on
the memories, so finitely many argument vectors give the budget, as they do
for runs in the set monad. The human ruled so on #373 on 2026-11-13
(`docs/decisions/semantics-refinement.md#refinement-with-memory`). A callee
that touches memory asks for the budget until
[#214](https://github.com/pmatos/funk/issues/214).

When the ops of a dialect ignore the memories where they touch none (the
section on touching no memory), every run of a function whose summary
touches no memory ignores the memories, calls and recursion included: each
way it ends from some memories, it ends from any others, with those others
in place of the memories it returns, which are the ones it started from.
The proof follows a run with memory op by op, by induction on its fuel, as
the soundness of summaries does. An op that runs by its own rule declares
no memory effect, since its function's summary declares none, so it ignores
the memories. A call runs its callee, whose summary is below its caller's,
from the caller's memories with a frame entered; the callee returns them as
they were, and leaving the frame gives back the caller's memories.

So such a function runs out of fuel from some memories exactly when it does
from any others, at the same budget, and finitely many argument vectors
bound its runs from given memories. Its runs from given memories are its
runs with memory: each way a run with memory ends, the run from any memories
ends the same way, with those memories.

Congruence in the callee for a dialect lawful in its monotonicity then
holds with no budget, for a callee with finitely many argument vectors
whose new body, in the new module, has a summary that touches no memory.
When the old callee's summary touches no memory too, refinement of their
runs with memory is refinement of their runs from given memories, so the
hypothesis can be stated over the runs with memory, as it was over the runs
in the set monad.
-/

namespace Fir

open SetM Memory

variable {d : Dialect} [DialectSignature d] [DialectCall d] [DialectEffects d]

/-! # Runs that ignore the memories -/

section

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem] [TyDenote d.Ty] [DecidableEq d.Ty]
  [DialectDenote d (StateT (Memories Mem unit) SetM)] {M : Module d}

omit [DialectEffects d] in
/-- A run in a call's frame ignores the memories when the run of its ops
does: entering the frame and leaving it gives back the memories it started
with. -/
theorem Func.memCall_ignoresMemory {n : Nat} {g : Func d} {genv : Env d}
    {body : List (Operation d)} {S T : Memories Mem unit}
    (hops : ∀ e, Ev.NotStuck e → (Func.memOps M n g genv body S.enter).run e →
      e.mapRet (atMemSteps S.enter) = e ∧
        (Func.memOps M n g genv body T.enter).run (e.mapRet (atMemSteps T.enter)))
    {e : Ev (Except Stuck (Result ((List (DVal d) × Memories Mem unit) × Nat)))}
    (hne : Ev.NotStuck e) (h : (Func.memCall M n g genv body S).run e) :
    e.mapRet (atMemSteps S) = e ∧ (Func.memCall M n g genv body T).run (e.mapRet (atMemSteps T)) := by
  rw [Func.memCall_eq] at h ⊢
  rcases (SetM.run_map _ _ _).1 h with ⟨a, ha, rfl⟩ | ⟨st, -, rfl⟩ | ⟨r, hr, rfl⟩
  · match a, ha with
    | .ret ((vs, U), k), ha =>
      obtain ⟨h1, h2⟩ := hops _ (Ev.notStuck_ok _) ha
      simp only [Ev.mapRet, atMemSteps, Ev.ok.injEq, Except.ok.injEq, Result.ret.injEq,
        Prod.mk.injEq, true_and, and_true] at h1
      subst h1
      exact ⟨rfl, (SetM.run_map _ _ _).2 (.inl ⟨_, h2, rfl⟩)⟩
    | .fuelExhausted, ha =>
      exact ⟨rfl, (SetM.run_map _ _ _).2 (.inl ⟨_, (hops _ (Ev.notStuck_ok _) ha).2, rfl⟩)⟩
  · exact absurd rfl (hne st)
  · exact ⟨rfl, (SetM.run_map _ _ _).2 (.inr (.inr ⟨r, (hops _ (Ev.notStuck_ub _) hr).2,
      rfl⟩))⟩

/-- Every run with memory of ops of a function of `M` whose summary touches
no memory ignores the memories, from any of its ops on, at any budget: each
way it ends from `S`, it ends from `T` too, with `T` in place of the
memories it returns, which are `S`. It asks that each op that runs by its
own rule and declares no memory effect ignore the memories. -/
theorem Module.memOps_ignoresMemory
    (hfree : OpsIgnoreMemory d Mem unit)
    (n : Nat) :
    ∀ (s : Name) (f : Func d) (env : Env d) (os : List (Operation d)) (S T : Memories Mem unit)
      (e : Ev (Except Stuck (Result ((List (DVal d) × Memories Mem unit) × Nat)))),
      M.func? s = some f → (M.table.summary s).TouchesNoMemory →
      (∀ o ∈ os, ∃ b ∈ f.blocks, o ∈ b.body) → Ev.NotStuck e →
      (Func.memOps M n f env os S).run e →
      e.mapRet (atMemSteps S) = e ∧ (Func.memOps M n f env os T).run (e.mapRet (atMemSteps T)) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro s f env os S T e hf hs hos hne h
  cases n with
  | zero =>
    obtain rfl := Func.run_memOps_zero.1 h
    exact ⟨rfl, Func.run_memOps_zero.2 rfl⟩
  | succ n =>
  cases os with
  | nil => exact absurd h (Func.run_memOps_nil hne)
  | cons o os =>
  obtain ⟨b, hb, ho⟩ := hos o List.mem_cons_self
  have hown : (effects o.op).TouchesNoMemory :=
    Effects.TouchesNoMemory.of_le (a := (effects o.op).callerView)
      (M.table.effects_le_summary hf (Func.mem_allOps hb ho)) hs
  have htail : ∀ o' ∈ os, ∃ b ∈ f.blocks, o' ∈ b.body :=
    fun o' h' => hos o' (List.mem_cons_of_mem _ h')
  have hneT := hne.mapRet (g := atMemSteps T)
  have callee : ∀ {c : Name} {g : Func d} {genv body} {dvs : List (DVal d)} {e'},
      callee? o.op = some c → isTerminator o.op = false → M.func? c = some g →
      g.enter dvs = .ok (body, genv) →
      Ev.NotStuck e' → (Func.memCall M n g genv body S).run e' →
      e'.mapRet (atMemSteps S) = e' ∧ (Func.memCall M n g genv body T).run (e'.mapRet (atMemSteps T)) :=
    fun {c g _ _ _ _} hc hT hg hen hne' hx => by
      have hg' : M.table.func? c = some g := hg
      have hcs : (M.table.summary c).TouchesNoMemory := Effects.TouchesNoMemory.of_le
        (M.table.summary_closed.calls s f hf o (Func.mem_allOps hb ho) c
          (Operation.call?_of hT hc) (by simp [hg'])) hs
      exact Func.memCall_ignoresMemory (fun e'' hne'' h'' => ih n (Nat.lt_succ_self n) c g _ _ _ _
        e'' hg hcs (Func.enter_ops hen).1 hne'' h'') hne' hx
  cases (Func.memStepPath_iff hne).1 h with
  | exitUB hreg hargs hT hos' hx =>
    exact ⟨rfl, (Func.memStepPath_iff hneT).2
      (.exitUB hreg hargs hT hos' (((hfree o.op (.inl hT) hown _).2 hT).1 S _ hx T))⟩
  | ret hreg hargs hT hos' hx hres =>
    obtain ⟨rfl, hx'⟩ := ((hfree o.op (.inl hT) hown _).2 hT).2 S _ _ hx
    exact ⟨rfl, (Func.memStepPath_iff hneT).2 (.ret hreg hargs hT hos' (hx' T) hres)⟩
  | goto hreg hargs hT hos' hx hj hrun =>
    obtain ⟨rfl, hx'⟩ := ((hfree o.op (.inl hT) hown _).2 hT).2 S _ _ hx
    obtain ⟨_, _, _, hblk, -⟩ := Func.jump_eq_ok hj
    obtain ⟨h1, h2⟩ := ih n (Nat.lt_succ_self n) s f _ _ _ T e hf hs
      (fun o' h' => ⟨_, (Func.block?_some hblk).1, h'⟩) hne hrun
    exact ⟨h1, (Func.memStepPath_iff hneT).2 (.goto hreg hargs hT hos' (hx' T) hj h2)⟩
  | denoteUB hreg hargs hT hc hx =>
    exact ⟨rfl, (Func.memStepPath_iff hneT).2
      (.denoteUB hreg hargs hT hc (((hfree o.op (.inr hc) hown _).1 hT).1 S _ hx T))⟩
  | denote hreg hargs hT hc hx hlen hrun =>
    obtain ⟨rfl, hx'⟩ := ((hfree o.op (.inr hc) hown _).1 hT).2 S _ _ hx
    obtain ⟨h1, h2⟩ := ih n (Nat.lt_succ_self n) s f _ os _ T e hf hs htail hne hrun
    exact ⟨h1, (Func.memStepPath_iff hneT).2 (.denote hreg hargs hT hc (hx' T) hlen h2)⟩
  | callUB hreg hargs hT hc hg hen hx =>
    exact ⟨rfl, (Func.memStepPath_iff hneT).2
      (.callUB hreg hargs hT hc hg hen (callee hc hT hg hen (Ev.notStuck_ub _) hx).2)⟩
  | callExh hreg hargs hT hc hg hen hx =>
    exact ⟨rfl, (Func.memStepPath_iff hneT).2
      (.callExh hreg hargs hT hc hg hen (callee hc hT hg hen (Ev.notStuck_ok _) hx).2)⟩
  | callRet hreg hargs hT hc hg hen hx hty hlen hrun =>
    obtain ⟨h1, hx'⟩ := callee hc hT hg hen (Ev.notStuck_ok _) hx
    simp only [Ev.mapRet, atMemSteps, Ev.ok.injEq, Except.ok.injEq, Result.ret.injEq,
      Prod.mk.injEq, true_and, and_true] at h1
    subst h1
    obtain ⟨h1, h2⟩ := ih _ (Nat.lt_succ_of_le (Nat.min_le_right _ _)) s f _ os _ T e hf hs htail
      hne hrun
    exact ⟨h1, (Func.memStepPath_iff hneT).2 (.callRet hreg hargs hT hc hg hen hx' hty hlen h2)⟩

/-- Every run from given memories of a function of `M` whose summary touches
no memory ignores the memories: each way it ends from `S`, it ends from `T`
too, with `T` in place of the memories it returns, which are `S`. -/
theorem Func.memRunsFrom_ignoresMemory
    (hfree : OpsIgnoreMemory d Mem unit)
    {s : Name} {f : Func d} (hf : M.func? s = some f) (hs : (M.table.summary s).TouchesNoMemory)
    (a : HVector toType (f.params.map (·.2))) (S T : Memories Mem unit) (n : Nat)
    {x : Ev (Except Stuck (Result (List (DVal d) × Memories Mem unit)))} (hne : Ev.NotStuck x)
    (h : f.memRunsFrom M (a, S) n x) :
    x.mapRet (atMem S) = x ∧ f.memRunsFrom M (a, T) n (x.mapRet (atMem T)) := by
  obtain ⟨p, hp, e, he, rfl⟩ := (Func.memRunsFrom_run hne).1 h
  have hne' : Ev.NotStuck e := fun st hst => by subst hst; exact hne st rfl
  obtain ⟨h1, h2⟩ := Func.memCall_ignoresMemory (fun e' hne'' h' =>
    Module.memOps_ignoresMemory hfree n s f p.2 p.1 S.enter T.enter e' hf hs (Func.enter_ops hp).1
      hne'' h') hne' he
  refine ⟨by rw [← Ev.dropLeft_mapRet, h1], (Func.memRunsFrom_run hne.mapRet).2
    ⟨p, hp, _, h2, (Ev.dropLeft_mapRet T e).symm⟩⟩

/-- A function of `M` whose summary touches no memory runs out of fuel from
some memories exactly when it does from any others, at the same budget. -/
theorem Func.memRunsFrom_exhausted_iff
    (hfree : OpsIgnoreMemory d Mem unit)
    {s : Name} {f : Func d} (hf : M.func? s = some f) (hs : (M.table.summary s).TouchesNoMemory)
    (a : HVector toType (f.params.map (·.2))) (S T : Memories Mem unit) (n : Nat) :
    (f.memRunsFrom M (a, S) n).outcomes .fuelExhausted ↔
      (f.memRunsFrom M (a, T) n).outcomes .fuelExhausted :=
  ⟨fun h => (Func.memRunsFrom_ignoresMemory hfree hf hs a S T n (Ev.notStuck_ok _) h).2,
    fun h => (Func.memRunsFrom_ignoresMemory hfree hf hs a T S n (Ev.notStuck_ok _) h).2⟩

/-- A function of `M` whose summary touches no memory and whose parameter
types have finitely many argument vectors has its runs from given memories
bounded by one budget: each argument vector has its own, and the memories
do not change it. -/
theorem Func.memRunsFrom_boundedBy_of_finite
    (hfree : OpsIgnoreMemory d Mem unit)
    {s : Name} {f : Func d} (hf : M.func? s = some f) (hs : (M.table.summary s).TouchesNoMemory)
    (hfin : ∃ L : List (HVector toType (f.params.map (·.2))), ∀ a, a ∈ L) :
    ∃ B, (f.memRunsFrom (Mem := Mem) (unit := unit) M).BoundedBy B := by
  obtain ⟨L, hL⟩ := hfin
  obtain ⟨B, hB⟩ := exists_common_bound hL
    (fun a m => (f.memRunsFrom M (a, (Memories.empty : Memories Mem unit)) m).outcomes
      .fuelExhausted)
    (fun _ _ _ hle hq => Func.memRunsFrom_exhausted_down hle hq)
  refine ⟨B, fun ⟨a, S⟩ => ?_⟩
  have hiff := Func.memRunsFrom_exhausted_iff hfree hf hs a S Memories.empty
  rcases hB a with h | h
  · exact .inl fun m => (hiff m).2 (h m)
  · exact .inr fun m hm hq => h m hm ((hiff m).1 hq)

end

end Fir
